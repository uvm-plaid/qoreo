
import sys
import os
import threading
import time
import traceback
import multiprocessing as mp
import random

from collections import Counter
from concurrent.futures import ProcessPoolExecutor

import numpy as np
import netsquid as ns


ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
PYTHON_DIR = os.path.join(ROOT, "python")
GENERATED_DIR = os.path.join(ROOT, "generated", "DQFT")

sys.path.insert(0, PYTHON_DIR)
sys.path.insert(0, GENERATED_DIR)

import qoreo_netsquid_runtime as qr
from app_alice import main as alice_main
from app_bob import main as bob_main
from app_charlie import main as charlie_main


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
    network = qr.QoreoNetwork(["alice", "bob", "charlie"])
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
    charlie_thread = threading.Thread(
        target=run_party,
        args=("charlie", charlie_main),
    )

    alice_thread.start()
    bob_thread.start()
    charlie_thread.start()

    while (
        alice_thread.is_alive()
        or bob_thread.is_alive()
        or charlie_thread.is_alive()
    ):
        with quantum_lock:
            ns.sim_run()
        time.sleep(0.001)

    alice_thread.join(timeout=1)
    bob_thread.join(timeout=1)
    charlie_thread.join(timeout=1)

    # Check for errors after all three threads finish
    if errors:
        raise RuntimeError(f"Party execution failed: {errors}")

    return results["alice"], results["bob"], results["charlie"]


def run_batch(job):
    worker_id, num_shots = job

    print(
        f"Worker {worker_id} (PID {os.getpid()}) started",
        flush=True,
    )

    seed = 20261026 + worker_id
    random.seed(seed)
    np.random.seed(seed)
    ns.set_random_state(seed=seed)

    counts = Counter()

    for i in range(num_shots):
        print(f"Worker {worker_id}: starting shot {i + 1}", flush=True)

        alice_result, bob_result, charlie_result = run_once()
        result = (alice_result, bob_result, charlie_result)
        counts[result] += 1

        print(f"Worker {worker_id}: completed shot {i + 1}", flush=True)

    print(f"Worker {worker_id}: finished", flush=True)

    return counts



if __name__ == "__main__":
    shots = 1000
    workers = 1

    workers = min(workers, shots)

    base, extra = divmod(shots, workers)

    jobs = [
        (i, base + (1 if i < extra else 0))
        for i in range(workers)
    ]

    counts = Counter()

    start_time = time.perf_counter()

    # We do this to count measurement results. We could just do alice_result, bob_result = run_once() if we don't want to run it multiple times
    with ProcessPoolExecutor(
        max_workers=workers,
        mp_context=mp.get_context("spawn"),
    ) as executor:
        for batch_counts in executor.map(run_batch, jobs):
            counts.update(batch_counts)

    elapsed_time = time.perf_counter() - start_time

    print("\nMEASUREMENT RESULTS:")
    for result, count in sorted(counts.items()):
        bitstring = "".join(
            str(bit)
            for actor_result in result
            for bit in actor_result)
        print(f"{bitstring}: {count}")

    print(f"\nTotal shots: {sum(counts.values())}")
    print(f"Worker processes: {workers}")
    print(f"Execution time: {elapsed_time:.2f} seconds")
