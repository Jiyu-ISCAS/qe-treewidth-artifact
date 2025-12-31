#!/usr/bin/env python3
"""
summarize_fme_results.py

Aggregate FME experiment results produced by the single-instance runner.

Input:
  One or more JSON files, each containing a list of result dictionaries.

Output:
  JSON summary with average final constraint count and runtime
  for each elimination strategy (random, greedy, heuristic).
"""

import argparse
import json
from typing import Dict, Any, List


def init_summary(order: str) -> Dict[str, Any]:
    return {
        "order": order,
        "success": 0,
        "abort": 0,
        "ave_cnt": 0.0,
        "ave_runtime": 0.0,
    }


def update_random_summary(summary: Dict[str, Any], result: Dict[str, Any]) -> None:
    """
    Update the random-summary: aborted runs are counted toward the
    ave_cnt / ave_runtime totals (but still increment 'abort').
    """
    if result.get("aborted"):
        summary["abort"] += 1
    else:
        summary["success"] += 1

    # include estimated (for aborted) or actual final_count (for success)
    summary["ave_cnt"] += result.get("final_count", 0)
    summary["ave_runtime"] += result.get("time_s", 0.0)


def update_summary(summary: Dict[str, Any], result: Dict[str, Any]) -> None:
    if result.get("aborted"):
        summary["abort"] += 1
    else:
        summary["success"] += 1
        summary["ave_cnt"] += result.get("final_count", 0)
        summary["ave_runtime"] += result.get("time_s", 0.0)


def finalize_random_summary(summary: Dict[str, Any]) -> None:
    summary["ave_cnt"] /= summary["success"] + summary["abort"]
    summary["ave_runtime"] /= summary["success"] + summary["abort"]


def finalize_summary(summary: Dict[str, Any]) -> None:
    if summary["success"] > 0:
        summary["ave_cnt"] /= summary["success"]
        summary["ave_runtime"] /= summary["success"]


def summarize_files(paths: List[str]) -> List[Dict[str, Any]]:
    random_summary = init_summary("random")
    greedy_summary = init_summary("greedy")
    heuristic_summary = init_summary("heuristic")

    for path in paths:
        with open(path, "r") as fh:
            data = json.load(fh)
        entries = data if isinstance(data, list) else [data]
        for entry in entries:
            if "result_random" in entry:
                update_random_summary(random_summary, entry["result_random"])
            if "result_greedy" in entry:
                update_summary(greedy_summary, entry["result_greedy"])
            if "result_heuristic" in entry:
                update_summary(heuristic_summary, entry["result_heuristic"])

    finalize_random_summary(random_summary)
    for s in (greedy_summary, heuristic_summary):
        finalize_summary(s)

    return [random_summary, greedy_summary, heuristic_summary]


if __name__ == "__main__":
    p = argparse.ArgumentParser(description="Summarize FME JSON result files")
    p.add_argument(
        "--inputs",
        nargs="+",
        help="JSON files produced by the FME runner",
    )
    p.add_argument(
        "--out",
        type=str,
        default="fme_summary.json",
        help="Output summary JSON file",
    )
    args = p.parse_args()

    summary = summarize_files(args.inputs)

    with open(args.out, "w") as fh:
        json.dump(summary, fh, indent=2)
