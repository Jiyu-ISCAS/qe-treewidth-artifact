import argparse
import json
import random
import re
from pathlib import Path
from typing import List, Optional, Dict, Any
from fme import parse_ine_file, run_fme


# regex helpers for parsing .ord content
_BRACE_RE = re.compile(r"\[([^}]+)\]")
_XTOKEN_RE = re.compile(r"x\s*(\d+)", re.IGNORECASE)
_INTS_RE = re.compile(r"\b\d+\b")


def parse_ord_file(path: Path) -> Optional[List[int]]:
    if not path.exists():
        return None
    try:
        txt = path.read_text().splitlines()
    except Exception:
        return None

    # NEW: look only for the specific line
    target_line = None
    for line in txt:
        if line.strip().startswith("Our heuristic"):
            target_line = line
            break

    if not target_line:
        return None

    # Extract [ ... ] content from that line
    m = _BRACE_RE.search(target_line)
    if not m:
        return None
    inside = m.group(1)
    xtoks = _XTOKEN_RE.findall(inside)
    if xtoks:
        return [int(n) - 1 for n in xtoks]

    ints = _INTS_RE.findall(inside)
    if ints:
        return [int(n) - 1 for n in ints]

    return None


def appearance_to_elim_filtered(
    subset_0: List[int], appearance_0: List[int]
) -> List[int]:
    """
    Convert appearance order (first listed = last to eliminate) into elimination order, then filter to subset.
    Steps:
      - full elimination order = reversed(appearance_0)
      - filtered = [v for v in full_elim if v in subset_0] (preserve relative order)
    """
    full_elim = list(appearance_0)
    sset = set(subset_0)
    return [v for v in full_elim if v in sset]


def to1based(lst: List[int]) -> List[int]:
    return [i + 1 for i in lst]


def run_random_trials_best(
    ineqs,
    order: List[int],
    seed: int,
    cap: int,
    n_trials: int,
) -> Dict[str, Any]:
    """
    Run N random permutations of `order`, return the best result
    (min time_s, tie-broken by min final_count).
    """
    rng = random.Random(seed)
    best = None
    aborted_candidates = []

    for _ in range(n_trials):
        perm = order[:]
        rng.shuffle(perm)

        trial_cap = cap
        if best is not None and best.get("final_count") is not None:
            # never increase cap; use the smaller of original cap and best final_count
            trial_cap = min(cap, best["final_count"])
        res = run_fme(ineqs, perm, greedy=False, cap=trial_cap)

        candidate = {
            "order": perm,
            "time_s": res.get("time_s"),
            "final_count": res.get("final_count"),
            "res": res,
        }

        if res.get("aborted"):
            # collect aborted trials so we can report their estimated value if all trials fail
            aborted_candidates.append(candidate)
            continue

        if best is None:
            best = candidate
        else:
            if candidate["final_count"] < best["final_count"] or (
                candidate["final_count"] == best["final_count"]
                and candidate["time_s"] < best["time_s"]
            ):
                best = candidate

    if best is not None:
        return {
            "aborted": False,
            "order": best["order"],
            "final_count": best["final_count"],
            "time_s": best["time_s"],
        }

    # no successful trial: return the best aborted candidate (smallest estimated)
    if aborted_candidates:
        aborted_candidates.sort(
            key=lambda c: (
                c["final_count"] if c["final_count"] is not None else float("inf"),
                c["time_s"] if c["time_s"] is not None else float("inf"),
            )
        )
        sel = aborted_candidates[0]
        return {
            "aborted": True,
            "order": sel["order"],
            "final_count": sel["final_count"],
            "time_s": sel["time_s"],
        }

    # fallback: no trials or no usable data
    return {"aborted": True}


def run_three_trials(
    ine_path: Path,
    ord_appearance: Optional[List[int]],
    order: List[int],
    seed: int,
    cap: int,
) -> Dict[str, Any]:
    """
    Run random, greedy, heuristic (if ord_appearance provided) experiments for one .ine file.
    Returns a summary dict.
    """
    ineqs = parse_ine_file(ine_path)
    if not ineqs:
        return {"file": str(ine_path), "error": "no inequalities parsed"}
    n_vars = len(ineqs[0][0])
    if n_vars == 0:
        return {"file": str(ine_path), "error": "no variables"}

    # A) random explicit permutation
    resA = run_random_trials_best(
        ineqs=ineqs,
        order=order,
        seed=seed,
        cap=cap,
        n_trials=5,
    )
    actualA = resA.get("order", [])

    # B) greedy within subset
    resB = run_fme(ineqs, order, greedy=True, cap=cap)
    actualB = [
        s["var_eliminated_original_index"]
        for s in resB.get("steps", [])
        if "var_eliminated_original_index" in s
    ]

    # C) heuristic from .ord (appearance -> elimination -> filter)
    if ord_appearance is not None:
        actualC = appearance_to_elim_filtered(order, ord_appearance)
        resC = run_fme(ineqs, actualC, greedy=False, cap=cap)
    else:
        actualC = []
        resC = {"aborted": True, "error": "no .ord found"}

    summary = {
        "file": str(ine_path),
        "n_vars": n_vars,
        "actual_best_random_order_used_1based": to1based(actualA),
        "result_random": {
            "aborted": resA.get("aborted"),
            "final_count": resA.get("final_count"),
            "time_s": resA.get("time_s"),
        },
        "actual_greedy_order_used_1based": to1based(actualB),
        "result_greedy": {
            "aborted": resB.get("aborted"),
            "final_count": resB.get("final_count"),
            "time_s": resB.get("time_s"),
        },
        "actual_heuristic_order_used_1based": to1based(actualC) if actualC else None,
        "result_heuristic": (
            {
                "aborted": resC.get("aborted"),
                "final_count": resC.get("final_count"),
                "time_s": resC.get("time_s"),
            }
        ),
    }
    return summary


if __name__ == "__main__":
    random_summary = {
        "order": "random",
        "success": 0,
        "abort": 0,
        "ave_cnt": 0,
        "ave_runtime": 0,
    }
    greedy_summary = {
        "order": "greedy",
        "success": 0,
        "abort": 0,
        "ave_cnt": 0,
        "ave_runtime": 0,
    }
    heuristic_summary = {
        "order": "heuristic",
        "success": 0,
        "abort": 0,
        "ave_cnt": 0,
        "ave_runtime": 0,
    }
    p = argparse.ArgumentParser(
        description="Run FME experiments using explicit .ord directory."
    )
    p.add_argument("--ine-input", type=Path, required=True, help=".ine file")
    p.add_argument(
        "--ord-input",
        type=Path,
        required=True,
        help="matching .ord files (same stem)",
    )
    p.add_argument(
        "--vars",
        type=str,
        required=True,
        help="Variables to be eliminated",
    )
    p.add_argument("--seed", type=int, default=42)
    p.add_argument("--cap", type=int, default=500000)
    p.add_argument("--output", type=str, default="fme_results.json")
    args = p.parse_args()

    ine_file = args.ine_input
    ord_file = args.ord_input

    results = []
    ord_appearance = parse_ord_file(ord_file) if ord_file.exists() else None
    if ord_appearance is None:
        print(
            f"  -> no valid .ord for {ine_file.name} at {ord_file} (heuristic run will be skipped)"
        )
    parts = [s.strip() for s in args.vars.split(",") if s.strip()]
    order_0based = [int(x) - 1 for x in parts]
    summary = run_three_trials(
        ine_path=ine_file,
        ord_appearance=ord_appearance,
        order=order_0based,
        seed=args.seed,
        cap=args.cap,
    )

    # write JSON
    with open(args.output, "w") as fh:
        json.dump(summary, fh, indent=2)
