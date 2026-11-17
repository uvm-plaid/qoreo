import os
import sys
import threading
import time

import netsquid as ns

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
PYTHON_DIR = os.path.join(ROOT, "python")
GENERATED_DIR = os.path.join(ROOT, "generated", "Simple_Routing_General")

sys.path.insert(0, PYTHON_DIR)
sys.path.insert(0, GENERATED_DIR)

import qoreo_netsquid_runtime as qr
from app_alice import main as alice_main
from app_bob import main as bob_main
from app_charlie import main as charlie_main
from app_david import main as david_main
from app_eve import main as eve_main
from app_frank import main as frank_main


# The lock synchronizes all the NetSquid threads.
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

parties = {
    "alice": alice_main,
    "bob": bob_main,
    "charlie": charlie_main,
    "david": david_main,
    "eve": eve_main,
    "frank": frank_main,}
    
def run_once():
    ns.sim_reset()
    network = qr.QoreoNetwork(list(parties))
    qr.set_network(network)
    results = {}
    errors = {}

    def run_party(party, main):
        try:
            results[party] = main()
        except Exception as exc:
            errors[party] = exc

    threads = {party: threading.Thread(
            target=run_party,
            args=(party, main),
            name=party,
            daemon=True,)
        for party, main in parties.items()}

    start = time.monotonic()
    for thread in threads.values():
        thread.start()
    while True:
        alive = [party for party, thread in threads.items() if thread.is_alive()]
        if errors:
            party, error = next(iter(errors.items()))
            raise RuntimeError(f"Actor {party} failed") from error
        if not alive:
            break
        if time.monotonic() - start > 20:
            raise TimeoutError(f"Routing protocol did not finish: {alive}")
        with quantum_lock:
            ns.sim_run()
        time.sleep(0.001)
    for thread in threads.values():
        thread.join()
    return tuple(results[party] for party in parties)


if __name__ == "__main__":
    shots = 5
    counts = {}
    start_time = time.perf_counter()

    for _ in range(shots):
        result = run_once()
        counts[result] = counts.get(result, 0) + 1

    elapsed_time = time.perf_counter() - start_time

    print("\nGENERAL ROUTING RESULTS:")
    for result, count in counts.items():
        alice, bob, charlie, david, eve, frank = result
        print(f"Alice: {alice}, "f"Bob: {bob}, "f"Charlie: {charlie}, "f"David: {david}, "f"Eve: {eve}, "f"Frank: {frank} "f"— {count}")

    print(f"\nTotal shots: {sum(counts.values())}")
    print(f"Execution time: {elapsed_time:.2f} seconds")