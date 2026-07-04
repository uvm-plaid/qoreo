import sys
import tempfile

sys.path.insert(0, "generated/b92")

from app_alice import main as alice_main
from app_bob import main as bob_main
from netqasm.runtime.application import Application, ApplicationInstance, Program
from netqasm.runtime.interface.config import default_network_config
from netqasm.sdk.config import LogConfig
from squidasm.run.multithread.runtime_mgr import SquidAsmRuntimeManager

NUM_RUNS = 5


def flatten_rounds(packed):
    """Convert (((r1,k1),(r2,k2)),(r3,k3)) into [(r1,k1),(r2,k2),(r3,k3)]."""
    (pair12, pair3) = packed
    (pair1, pair2) = pair12
    return [pair1, pair2, pair3]


def extract_key(packed):
    """Return the key bits from conclusive rounds (those where the result bit is 1)."""
    return [int(key_bit) for result, key_bit in flatten_rounds(packed) if result == 1]


def run_once():
    network_cfg = default_network_config(["alice", "bob"])
    mgr = SquidAsmRuntimeManager()
    mgr.set_network(network_cfg)
    mgr.start_backend()

    prog_alice = Program(party="alice", entry=alice_main, args=["app_config"], results=[])
    prog_bob = Program(party="bob", entry=bob_main, args=["app_config"], results=[])
    app = Application(programs=[prog_alice, prog_bob], metadata=None)

    with tempfile.TemporaryDirectory() as log_dir:
        log_cfg = LogConfig(
            track_lines=False,
            log_subroutines_dir=log_dir,
            comm_log_dir=log_dir,
        )
        app_instance = ApplicationInstance(
            app=app,
            program_inputs={"alice": {}, "bob": {}},
            network=None,
            party_alloc={"alice": "alice", "bob": "bob"},
            logging_cfg=log_cfg,
        )
        results = mgr.run_app(app_instance)

    mgr.stop_backend()
    return results


def main():
    for run_index in range(NUM_RUNS):
        results = run_once()
        alice_key = extract_key(results["app_alice"])
        bob_key = extract_key(results["app_bob"])

        assert alice_key == bob_key, (
            f"Run {run_index + 1}: key mismatch! alice={alice_key} bob={bob_key}"
        )
        print(f"Run {run_index + 1}: key = {alice_key}")


if __name__ == "__main__":
    main()
