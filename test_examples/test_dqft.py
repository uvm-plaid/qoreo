import sys
import os
import threading
import time
import traceback

import netsquid as ns


ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
PYTHON_DIR = os.path.join(ROOT, "python")
GENERATED_DIR = os.path.join(ROOT, "generated", "DQFT")

sys.path.insert(0, PYTHON_DIR)
sys.path.insert(0, GENERATED_DIR)

import qoreo_netsquid_runtime as qr
from app_alice import main as alice_main
from app_bob import main as bob_main


# The locks were added here to prevent NetSquid from crashing from improper memory usage.
quantum_lock = threading.RLock()

original_unitary = qr.Unitary
original_meas = qr.Runtime.Meas
original_new = qr.Runtime.new


def synchronized_unitary(*args, **kwargs):
    with quantum_lock:
        return original_unitary(*args, **kwargs)


def synchronized_meas(self, qubit):
    with quantum_lock:
        return original_meas(self, qubit)


def synchronized_new(self, value):
    with quantum_lock:
        return original_new(self, value)


qr.Unitary = synchronized_unitary
qr.Runtime.Meas = synchronized_meas
qr.Runtime.new = synchronized_new


# SquidASM uses threads on its own backend. In our NetQASM code, when we called
# app = Application(programs=[prog_alice, prog_bob], metadata=None) for example,
# app_alice and app_bob ran on separate threads.
# NetSquid doesn't intrinsically have that behavior so we're writing that ourselves.
def run_once():
    ns.sim_reset()
    network = qr.QoreoNetwork(["alice", "bob"])
    qr.set_network(network)

    results = {}
    errors = {}

    def run_party(party, main):
        try:
            results[party] = main()
        except Exception as exc:
            errors[party] = exc
            traceback.print_exc()

    alice_thread = threading.Thread(
        target=run_party,
        args=("alice", alice_main),
    )
    bob_thread = threading.Thread(
        target=run_party,
        args=("bob", bob_main),
    )

    alice_thread.start()
    bob_thread.start()
    while alice_thread.is_alive() or bob_thread.is_alive():
        with quantum_lock:
            ns.sim_run()

    time.sleep(0.001)
    #while alice_thread.is_alive() or bob_thread.is_alive():
    #    ns.sim_run()
    #    time.sleep(0.001)

    alice_thread.join(timeout=1)
    bob_thread.join(timeout=1)

    # Check for errors after both threads finish
    if errors:
        raise RuntimeError(f"Party execution failed: {errors}")

    return results["alice"], results["bob"]



if __name__ == "__main__":
    shots = 1000 #1000
    counts = {}
    # We do this to count measurement results. We could just do alice_result, bob_result = run_once() if we don't want to run it multiple times
    for _ in range(shots):
        alice_result, bob_result = run_once()

        result = (alice_result, bob_result)
        counts[result] = counts.get(result, 0) + 1
    #Print statements need to be modified for different qubit counts - Not optimal
    print("\nMEASUREMENT RESULTS:")
    for result, count in sorted(counts.items()):
        (alice1, alice2, alice3), (bob1,bob2,bob3)  = result
        #alice, (bob1, bob2) = result
        print(f"{alice1}{alice2}{alice3}{bob1}{bob2}{bob3}: {count}")