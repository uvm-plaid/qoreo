
import sys
import os
import threading
import time
import traceback
import faulthandler

import netsquid as ns

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
PYTHON_DIR = os.path.join(ROOT, "python")
GENERATED_DIR = os.path.join(ROOT, "generated", "Simple_Routing")

sys.path.insert(0, PYTHON_DIR)
sys.path.insert(0, GENERATED_DIR)

import qoreo_netsquid_runtime as qr
from app_alice import main as alice_main
from app_bob import main as bob_main
from app_charlie import main as charlie_main
from app_david import main as david_main
from app_eve import main as eve_main
from app_frank import main as frank_main


# Synchronize quantum operations across actor threads.
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


original_send = qr.Runtime.send
original_recv = qr.Runtime.recv


def debug_send(self, *args, **kwargs):
    party = threading.current_thread().name

    print(
        f"[{party}] SEND START: {args}",
        flush=True,
    )

    result = original_send(self, *args, **kwargs)

    print(
        f"[{party}] SEND DONE: {args}",
        flush=True,
    )

    return result


def debug_recv(self, *args, **kwargs):
    party = threading.current_thread().name

    print(
        f"[{party}] RECV WAIT: {args}",
        flush=True,
    )

    value = original_recv(self, *args, **kwargs)

    print(
        f"[{party}] RECV DONE: {args} -> {value}",
        flush=True,
    )

    return value


qr.Runtime.send = debug_send
qr.Runtime.recv = debug_recv

qr.Unitary = synchronized_unitary
qr.Runtime.Meas = synchronized_meas
qr.Runtime.new = synchronized_new


# All six actors in the nested conditional routing protocol.
parties = {
    "alice": alice_main,
    "bob": bob_main,
    "charlie": charlie_main,
    "david": david_main,
    "eve": eve_main,
    "frank": frank_main,
}


def run_once():
    ns.sim_reset()

    network = qr.QoreoNetwork(list(parties.keys()))
    qr.set_network(network)

    results = {}
    errors = {}

    def run_party(party, main):
        print(f"{party}: started", flush=True)

        try:
            results[party] = main()
            print(f"{party}: finished", flush=True)

        except Exception as exc:
            errors[party] = exc
            print(f"{party}: ERROR - {exc}", flush=True)
            traceback.print_exc()

    threads = {}

    for party, main in parties.items():
        threads[party] = threading.Thread(
            target=run_party,
            args=(party, main),
            name=party,
            daemon=True,
        )

    faulthandler.enable()
    faulthandler.dump_traceback_later(15, repeat=False)

    start = time.monotonic()

    try:
        for thread in threads.values():
            thread.start()

        while True:
            alive = [
                party
                for party, thread in threads.items()
                if thread.is_alive()
            ]

            if errors:
                raise RuntimeError(
                    f"Actor execution failed: {errors}"
                )

            if not alive:
                break

            if time.monotonic() - start > 20:
                print(
                    f"\nTIMEOUT: Actors still running: {alive}",
                    flush=True,
                )

                faulthandler.dump_traceback(
                    file=sys.stderr,
                    all_threads=True,
                )

                raise TimeoutError(
                    f"Routing protocol did not finish: {alive}"
                )

            with quantum_lock:
                ns.sim_run()

            time.sleep(0.001)

        for thread in threads.values():
            thread.join()

        return tuple(
            results[party] for party in parties
        )

    finally:
        faulthandler.cancel_dump_traceback_later()


if __name__ == "__main__":
    shots = 1
    counts = {}

    start_time = time.perf_counter()

    for i in range(shots):
        print(
            f"\n========== SHOT {i + 1} ==========",
            flush=True,
        )

        result = run_once()

        counts[result] = counts.get(result, 0) + 1

    elapsed_time = time.perf_counter() - start_time

    print("\nSIMPLE ROUTING RESULTS:")

    for result, count in sorted(counts.items()):
        alice, bob, charlie, david, eve, frank = result

        print(
            f"Alice: {alice}, "
            f"Bob: {bob}, "
            f"Charlie: {charlie}, "
            f"David: {david}, "
            f"Eve: {eve}, "
            f"Frank: {frank} "
            f"— {count}"
        )

    print(f"\nTotal shots: {sum(counts.values())}")
    print(f"Execution time: {elapsed_time:.2f} seconds")
