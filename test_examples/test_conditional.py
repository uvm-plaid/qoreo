
import sys
import os
import threading
import time

import netsquid as ns

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
PYTHON_DIR = os.path.join(ROOT, "python")
GENERATED_DIR = os.path.join(ROOT, "generated", "conditional_test")

sys.path.insert(0, PYTHON_DIR)
sys.path.insert(0, GENERATED_DIR)

import qoreo_netsquid_runtime as qr
from app_alice import main as alice_main
from app_bob import main as bob_main
from app_charlie import main as charlie_main


def run_once():
    ns.sim_reset()
    network = qr.QoreoNetwork(["alice", "bob", "charlie"])
    qr.set_network(network)

    results = {}

    def run_party(party, main):
        results[party] = main()

    alice_thread = threading.Thread(
        target=run_party, args=("alice", alice_main)
    )
    bob_thread = threading.Thread(
        target=run_party, args=("bob", bob_main)
    )
    charlie_thread = threading.Thread(
        target=run_party, args=("charlie", charlie_main)
    )

    alice_thread.start()
    bob_thread.start()
    charlie_thread.start()

    while (alice_thread.is_alive() or
           bob_thread.is_alive() or
           charlie_thread.is_alive()):
        ns.sim_run()
        time.sleep(0.001)

    alice_thread.join(timeout=1)
    bob_thread.join(timeout=1)
    charlie_thread.join(timeout=1)

    return results["alice"], results["bob"], results["charlie"]


if __name__ == "__main__":
    shots = 100
    counts = {}

    for _ in range(shots):
        alice_result, bob_result, charlie_result = run_once()

        result = (alice_result, bob_result, charlie_result)
        counts[result] = counts.get(result, 0) + 1

    print("\nCONDITIONAL TEST RESULTS:")
    for result, count in sorted(counts.items()):
        alice, bob, charlie = result
        print(f"Alice: {alice}, Bob: {bob}, Charlie: {charlie} — {count}")
