import sys
import os
import threading
import time
import traceback

import netsquid as ns


ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
PYTHON_DIR = os.path.join(ROOT, "python")
GENERATED_DIR = os.path.join(ROOT, "generated", "unitary_test")

sys.path.insert(0, PYTHON_DIR)
sys.path.insert(0, GENERATED_DIR)

import qoreo_netsquid_runtime as qr
from app_alice import main as alice_main
NUM_RUNS = 10


def run_once():
    ns.sim_reset()
    network = qr.QoreoNetwork(["alice"])
    qr.set_network(network)

    results = {}

    def run_party(party, main):
        results[party] = main()

    alice_thread = threading.Thread(
        target=run_party,
        args=("alice", alice_main),
    )

    alice_thread.start()

    while alice_thread.is_alive():
        ns.sim_run()
        time.sleep(0.001)

    alice_thread.join(timeout=1)
    #bob_thread.join(timeout=1)

    return results["alice"]



def main():
    expected = (((0, 0), (1, 0)), (0, 0))

    for run_index in range(NUM_RUNS):
        results = run_once()

        actual = results

       
        assert actual == expected

    print(f"\nAll {NUM_RUNS} runs passed.")
    print("Tdag: WORKS")
    print("Sdag: WORKS")
    print("CS:   WORKS")
    print("CT:   WORKS")
    print("CSdag: WORKS")
    print("CTdag: WORKS")


if __name__ == "__main__":
    main()