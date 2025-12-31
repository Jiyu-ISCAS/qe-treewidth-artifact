import argparse
import signal
import sys
import time
from smt2graph_utils import *


class TimeoutException(Exception):
    """Raised when execution exceeds the time limit."""

    pass


def _timeout_handler(signum, frame):
    raise TimeoutException("Timeout")


DEFAULT_LOG = Path("smt2graph.log")
DEFAULT_VERTEX_THRESHOLD = 10000


def parse_args(argv: list[str]) -> argparse.Namespace:
    p = argparse.ArgumentParser(
        description="Convert SMT2 inputs into graphs and formulas."
    )
    p.add_argument("--input", type=Path, help="Directory for SMT2 inputs")
    p.add_argument(
        "--intermediate-output",
        type=Path,
        help="Directory for renamed formulas and substitution maps",
    )
    p.add_argument(
        "--gr-output", type=Path, help="Directory for graphs for tree decomposition"
    )
    p.add_argument(
        "--time", type=int, help="Per-file timeout in seconds (0 = no limit)"
    )
    p.add_argument("--log-path", type=Path, default=DEFAULT_LOG)
    p.add_argument("--vertex-threshold", type=int, default=DEFAULT_VERTEX_THRESHOLD)
    return p.parse_args(argv)


if __name__ == "__main__":
    ns = parse_args(sys.argv[1:])
    signal.signal(signal.SIGALRM, _timeout_handler)

    files = iter_files(ns.input)
    ns.intermediate_output.mkdir(parents=True, exist_ok=True)
    with open(ns.log_path, "w") as log:
        log.write("")

    start = time.time()
    for rel_dir, name in files:
        if not str(name).lower().endswith(".smt2"):
            continue
        smt2_input = ns.input / rel_dir / name
        try:
            # Arm an alarm (seconds)
            signal.alarm(ns.time)
            G, subs_map, merged_asserts = parse_smt2_file(smt2_input)
            # Disarm the alarm as soon as function returns
            signal.alarm(0)

            num_vertices = G.number_of_nodes()
            num_edges = G.number_of_edges()

            # Discard large graphs and complete graphs
            if (
                num_vertices > ns.vertex_threshold
                or num_vertices * (num_vertices - 1) == 2 * num_edges
            ):
                continue
            print_results(
                name,
                G,
                subs_map,
                merged_asserts,
                ns.intermediate_output / rel_dir,
                ns.gr_output,
            )

        except TimeoutException as e:
            with open(ns.log_path, "a") as log:
                log.write(f"{e}: {smt2_input}\n")
        except TypeError as e:
            with open(ns.log_path, "a") as log:
                log.write(f"{e}: {smt2_input}\n")
        except:
            with open(ns.log_path, "a") as log:
                log.write(f"Other pysmt errors: {smt2_input}\n")

    end = time.time()
    with open(ns.log_path, "a") as log:
        log.write(f"Total runtime {end-start:.4f} s.\n")
