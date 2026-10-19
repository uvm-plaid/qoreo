
import sys
import os
import threading
import time
import traceback

import netsquid as ns

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
PYTHON_DIR = os.path.join(ROOT, "python")
GENERATED_DIR = os.path.join(ROOT, "generated", "DistributedGrover")

sys.path.insert(0, PYTHON_DIR)
sys.path.insert(0, GENERATED_DIR)

import qoreo_netsquid_runtime as qr
from app_alice import main as alice_main
from app_bob import main as bob_main


def run_once():
    ns.sim_reset()

    network = qr.QoreoNetwork(["alice", "bob"])
    qr.set_network(network)

    results = {}
    errors = {}

    def run_party(party, main):
        try:
            results[party] = main()
        except Exception:
            errors[party] = traceback.format_exc()

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
        ns.sim_run()
        time.sleep(0.001)

    alice_thread.join(timeout=1)
    bob_thread.join(timeout=1)

    if errors:
        raise RuntimeError(
            "\n".join(
                f"{party} failed:\n{error}"
                for party, error in errors.items()
            )
        )

    return results["alice"], results["bob"]


if __name__ == "__main__":
    shots = 32 #1000
    counts = {}

    for _ in range(shots):
        alice_result, bob_result = run_once()

        # Alice and Bob each own 1 qubit.
        result = (int(alice_result), int(bob_result))
        counts[result] = counts.get(result, 0) + 1

    print("\nDISTRIBUTED GROVER RESULTS")
    print("Marked state: |11>")
    print(f"Shots: {shots}\n")

    for a in (0, 1):
        for b in (0, 1):
            count = counts.get((a, b), 0)
            print(f"{a}{b}: {count}")

    success = counts.get((1, 1), 0)
    print(f"\nSuccess probability: {success / shots:.2%}")
