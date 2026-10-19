
import sys
import os
import threading
import time
import math

import netsquid as ns

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
PYTHON_DIR = os.path.join(ROOT, "python")
GENERATED_DIR = os.path.join(ROOT, "generated", "UnitaryTest")

sys.path.insert(0, GENERATED_DIR)
sys.path.insert(0, PYTHON_DIR)

import qoreo_netsquid_runtime as qr
print("Runtime:", qr.__file__, flush=True)
from app_alice import main as alice_main

NUM_RUNS = 1000

TEST_NAMES = [
    "Tdag",
    "Sdag",
    "CS",
    "CT",
    "CSdag",
    "CTdag",
    "RZ vs T",
    "RZ arbitrary inverse",
    "RZ probability",
    "CRZ inverse",
    "CRZ probability",
]

EXPECTED = {
    "Tdag": 0,
    "Sdag": 0,
    "CS": 1,
    "CT": 0,
    "CSdag": 0,
    "CTdag": 0,
    "RZ vs T": 0,
    "RZ arbitrary inverse": 0,
    "CRZ inverse": 0,
}

EXPECTED_P1 = math.sin(3 * math.pi / 14) ** 2


def run_once():
    ns.sim_reset()
    network = qr.QoreoNetwork(["alice"])
    qr.set_network(network)

    results = {}
    errors = {}

    def run_party(party, main):
        try:
            results[party] = main()
        except Exception as exc:
            errors[party] = exc

    alice_thread = threading.Thread(
        target=run_party,
        args=("alice", alice_main),
    )
    alice_thread.start()

    while alice_thread.is_alive():
        ns.sim_run()
        time.sleep(0.001)

    alice_thread.join()

    if errors:
        raise RuntimeError("Alice execution failed") from errors["alice"]

    return results["alice"]


def flatten(value):
    """Convert nested Pair results into a flat list."""
    if isinstance(value, (tuple, list)):
        output = []
        for item in value:
            output.extend(flatten(item))
        return output
    return [value]


def main():
    counts = {
        name: {0: 0, 1: 0}
        for name in TEST_NAMES
    }

    for run_index in range(NUM_RUNS):
        result = run_once()
        measurements = flatten(result)

        assert len(measurements) == len(TEST_NAMES), (
            f"Expected {len(TEST_NAMES)} results, "
            f"received {len(measurements)}: {result}"
        )

        run_results = dict(zip(TEST_NAMES, measurements))

        # Print the actual measurement from each test on the first run.
        if run_index == 0:
            print("\nFirst run measurements:")
            for name, value in run_results.items():
                print(f"  {name:<22}: {value}")

        for name, value in run_results.items():
            assert value in (0, 1), (
                f"Unexpected measurement for {name}: {value}"
            )

            counts[name][value] += 1

            if name in EXPECTED:
                assert value == EXPECTED[name], (
                    f"Run {run_index + 1}: {name} failed. "
                    f"Expected {EXPECTED[name]}, got {value}"
                )

    print(f"\nResults across {NUM_RUNS} runs:")
    
    print(f"{'Test':<23} {'0 count':>9} {'1 count':>9} {'Status':>12}")
    

    for name in TEST_NAMES:
        zeros = counts[name][0]
        ones = counts[name][1]
        status = "PASS" if name in EXPECTED else "SAMPLED"
        print(f"{name:<23} {zeros:>9} {ones:>9} {status:>12}")

    # Verify both RZ and CRZ probability distributions.
    for name in ("RZ probability", "CRZ probability"):
        observed_p1 = counts[name][1] / NUM_RUNS
        standard_error = math.sqrt(
            EXPECTED_P1 * (1 - EXPECTED_P1) / NUM_RUNS
        )

        print(f"\n{name}:")
        print(f"  Expected P(1): {EXPECTED_P1:.4%}")
        print(f"  Observed P(1): {observed_p1:.4%}")
        print(f"  Standard error: {standard_error:.4%}")

        tolerance = 5 * standard_error

        assert abs(observed_p1 - EXPECTED_P1) <= tolerance, (
            f"{name} probability distribution differs substantially "
            f"from the expected distribution."
        )

    print("\nAll deterministic tests passed.")
    print("RZ and CRZ probability distributions passed statistical checks.")


if __name__ == "__main__":
    main()
