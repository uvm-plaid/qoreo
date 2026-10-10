from __future__ import annotations

from contextlib import contextmanager
from typing import Any
from queue import Queue
import numpy as np
import netsquid as ns

from netsquid.nodes import Node, Network
from netsquid.components import ClassicalChannel, QuantumChannel
from netsquid.components.qprocessor import QuantumProcessor
from netsquid.protocols import NodeProtocol
from netsquid.qubits import create_qubits, qubitapi as qapi, ketstates as ks
from netsquid.qubits.operators import Operator

# Added support for gates not inbuilt in NetSquid 
S = Operator("S", np.diag([1, 1j]))
Sdag = Operator("Sdag", np.diag([1, -1j]))
T = Operator("T", np.diag([1, np.exp(1j * np.pi / 4)]))
Tdag = Operator("Tdag", np.diag([1, np.exp(-1j * np.pi / 4)]))
CS = Operator("CS", np.diag([1, 1, 1, 1j]))
CSdag = Operator("CSdag", np.diag([1, 1, 1, -1j]))
CT = Operator("CT", np.diag([1, 1, 1, np.exp(1j * np.pi / 4)]))
CTdag = Operator("CTdag", np.diag([1, 1, 1, np.exp(-1j * np.pi / 4)]))


def Unitary(gate: str, value: Any) -> Any:
    gates = {
        "H": ns.H, "X": ns.X, "Y": ns.Y, "Z": ns.Z,
        "SGATE": S, "TGATE": T, "Sdag": Sdag, "Tdag": Tdag,
    }

    controlled_gates = {
        "CNOT": ns.CNOT,
        "CS": CS, "CSdag": CSdag,
        "CT": CT, "CTdag": CTdag,
    }

    if gate in controlled_gates:
        if not isinstance(value, tuple) or len(value) != 2:
            raise TypeError(f"{gate} expects a pair of qubits, got {value!r}")

        control, target = value
        qapi.operate([control, target], controlled_gates[gate])
        return control, target

    if gate in gates:
        qapi.operate(value, gates[gate])
        return value

    raise NotImplementedError(f"unsupported unitary: {gate}")


class Receiver(NodeProtocol):
    def __init__(self, node, port, queue):
        super().__init__(node)
        self.port = port
        self.queue = queue

    def run(self):
        while True:
            yield self.await_port_input(self.port)
            message = self.port.rx_input() 
            #We use queues here so that our classical input is assigned to a variable that matches the generated structure
            self.queue.put(message.items[0])


_ACTIVE_NETWORK = None


def set_network(network):
    global _ACTIVE_NETWORK
    _ACTIVE_NETWORK = network


class QoreoNetwork:
    def __init__(self, parties):
        self.parties = parties
        self.network = Network("QoreoNetwork")

        # Assign a QPU for each party.
        self.nodes = {}
        for party in parties:
            qpu = QuantumProcessor(
                f"{party}_qpu",
                num_positions=10, #TO DO: Change this to be an argument so we can manually allocate Qubit memory
                fallback_to_nonphysical=True,
            )
            self.nodes[party] = Node(party, qmemory=qpu)
            self.network.add_node(self.nodes[party])
        # Taken directly from: https://docs.netsquid.org/latest-release/api_nodes/netsquid.nodes.network.html#netsquid.nodes.network.Network.add_connection
        # Initialize classical channels for each set of parties
        self.classical_ports = {}

        for sender in parties:
            for receiver in parties:
                if sender == receiver:  # So Alice can't send to Alice!
                    continue

                self.classical_ports[(sender, receiver)] = self.network.add_connection(
                    self.nodes[sender],
                    self.nodes[receiver],
                    channel_to=ClassicalChannel(
                        f"{sender}_to_{receiver}",
                        delay=1,
                    ),
                    label=f"{sender}_to_{receiver}",
                )

        # Quantum channels for EPR distribution. NOTE: This doesn't create EPRs as soon as the 
        # Network is initialized, it just tells the network who receives what 
        # when the epr() function is called
        self.epr_source = Node("epr_source")
        self.network.add_node(self.epr_source)
        
        self.epr_ports = {}

        for party in parties:
            self.epr_ports[party] = self.network.add_connection(
                self.epr_source,
                self.nodes[party],
                channel_to=QuantumChannel(
                    f"epr_to_{party}",
                    delay=1,
                ),
                label=f"epr_{party}",
            )

        # Classical queues. TO DO: See if we can bypass using Queues
        self.classical_queues = {
            (sender, receiver): Queue()
            for sender in parties
            for receiver in parties
            if sender != receiver
        }

        # EPR queues.
        self.epr_queues = {
            party: Queue()
            for party in parties
        }

        self.protocols = []

        # Classical receivers.
        for sender, receiver in self.classical_queues:
            _, receiver_port = self.classical_ports[(sender, receiver)]

            protocol = Receiver(
                self.nodes[receiver],
                self.nodes[receiver].ports[receiver_port],
                self.classical_queues[(sender, receiver)],
            )

            protocol.start()
            self.protocols.append(protocol)

        # EPR receivers.
        for party in parties:
            _, receiver_port = self.epr_ports[party]

            protocol = Receiver(
                self.nodes[party],
                self.nodes[party].ports[receiver_port],
                self.epr_queues[party],
            )

            protocol.start()
            self.protocols.append(protocol)

    def send(self, sender, receiver, value):
        sender_port, _ = self.classical_ports[(sender, receiver)]
        self.nodes[sender].ports[sender_port].tx_output(value)

    def recv(self, receiver, sender):
        return self.classical_queues[(sender, receiver)].get()
    # We mimic the same behavior from the NetQASM code. Only 1 party is responsible for creating the EPR pair, in this case Alice.
    # When Bob runs rt.epr("alice"), he only receives his half of the epr pair created by Alice.
    def epr(self, party, peer):
        if party < peer:
            q0, q1 = create_qubits(2, no_state=True)
            qapi.assign_qstate([q0, q1], ks.b00)

            party_port, peer_port = self.epr_ports[party][0], self.epr_ports[peer][0]

            self.epr_source.ports[party_port].tx_output(q0)
            self.epr_source.ports[peer_port].tx_output(q1)

        qubit = self.epr_queues[party].get()

        position = self.nodes[party].qmemory.unused_positions[0]
        self.nodes[party].qmemory.put(qubit, positions=position)

        return qubit


class Runtime:
    def __init__(
        self,
        party: str,
        app_config: Any = None,
        classical_peers: list[str] | None = None,
        epr_peers: list[str] | None = None,
    ):
        if _ACTIVE_NETWORK is None:
            raise RuntimeError("No active QoreoNetwork.")

        self.party = party
        self.app_config = app_config
        self.classical_peers = classical_peers or []
        self.epr_peers = epr_peers or []
        self.network = _ACTIVE_NETWORK
        self.node = self.network.nodes[party]

    @contextmanager
    def connection(self):
        yield self

    def new(self, value: bool):
        position = self.node.qmemory.unused_positions[0]
        qubit = create_qubits(1)[0]
        self.node.qmemory.put(qubit, positions=position)

        if value:
            qapi.operate(qubit, ns.X)

        return qubit
    # Meas also lets me return measurement probabilities, something we couldn't do in NetQASM.
    # Can/Should we change renderer so it can also accept this?
    def Meas(self, qubit) -> int:
        result, _ = qapi.measure(qubit)
        return int(result)

    def flush(self):
        pass

    def send(self, peer: str, value: Any):
        self.network.send(self.party, peer, value)

    def recv(self, peer: str) -> int:
        return int(self.network.recv(self.party, peer))

    def epr(self, peer: str):
        return self.network.epr(self.party, peer)