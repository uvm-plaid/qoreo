from __future__ import annotations

from contextlib import contextmanager
from typing import Any

from netqasm.sdk import EPRSocket, Qubit
from netqasm.sdk.external import NetQASMConnection, Socket

def Unitary(gate: str, value: Any) -> Any:
    if gate == "CNOT":
        if not isinstance(value, tuple) or len(value) != 2:
            raise TypeError(f"CNOT expects a pair of qubits, got {value!r}")
        control, target = value
        control.cnot(target)
        return (control, target)

    if gate == "H":
        value.H()
        return value
    if gate == "X":
        value.X()
        return value
    if gate == "Y":
        value.Y()
        return value
    if gate == "Z":
        value.Z()
        return value
    if gate == "SGATE":
        value.S()
        return value
    if gate == "TGATE":
        value.T()
        return value

    raise NotImplementedError(f"unsupported unitary: {gate}")


class Runtime:
    def __init__(
        self,
        party: str,
        app_config: Any,
        classical_peers: list[str],
        epr_peers: list[str],
    ) -> None:
        self.party = party
        self.app_config = app_config
        self.classical_peers = classical_peers
        self.epr_peers = epr_peers
        self.sockets = {
            peer: Socket(party, peer, log_config=app_config.log_config)
            for peer in classical_peers
        }
        self.epr_sockets = {peer: EPRSocket(peer) for peer in epr_peers}
        self.conn: NetQASMConnection | None = None

    @contextmanager
    def connection(self):
        with NetQASMConnection(
            self.party,
            log_config=self.app_config.log_config,
            epr_sockets=[self.epr_sockets[peer] for peer in self.epr_peers],
        ) as conn:
            self.conn = conn
            try:
                yield self
            finally:
                self.conn = None

    def new(self, value: bool) -> Qubit:
        if self.conn is None:
            raise RuntimeError("runtime connection is not active")
        qubit = Qubit(self.conn)
        if value:
            qubit.X()
        return qubit

    def Meas(self, qubit: Qubit) -> int:
        result = qubit.measure()
        self.flush()
        return int(result)

    def flush(self) -> None:
        if self.conn is None:
            raise RuntimeError("runtime connection is not active")
        self.conn.flush()

    def send(self, peer: str, value: Any) -> None:
        self.sockets[peer].send(str(value))

    def recv(self, peer: str) -> int:
        self.flush()
        return int(self.sockets[peer].recv())

    def epr(self, peer: str) -> Qubit:
        socket = self.epr_sockets[peer]
        if self.party < peer:
            return socket.create_keep()[0]
        return socket.recv_keep()[0]
