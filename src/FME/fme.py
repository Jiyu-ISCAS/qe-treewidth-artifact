import argparse, re, time, json
from fractions import Fraction
from pathlib import Path


# ----------------------
# parse .ine H-format
# ----------------------
def parse_ine_file(path):
    rows = []
    with open(path, "r") as fh:
        for raw in fh:
            s = raw.strip()
            if not s:
                continue
            low = s.lower()
            if (
                low.startswith("begin")
                or low.startswith("end")
                or low.startswith("h-representation")
            ):
                continue
            if s.startswith("*") or s.startswith("#") or s.startswith("%"):
                continue
            parts = s.split()
            nums = []
            for tok in parts:
                if re.match(r"[-+]?\d+$", tok) or re.match(r"[-+]?\d+/\d+$", tok):
                    nums.append(tok)
                else:
                    break
            if not nums:
                continue
            if len(nums) in (2, 3) and not rows:
                continue
            parsed = []
            for tok in nums:
                if "/" in tok:
                    a, b = tok.split("/")
                    parsed.append(Fraction(int(a), int(b)))
                else:
                    parsed.append(Fraction(int(tok)))
            if len(parsed) >= 2:
                b = parsed[0]
                coeffs = parsed[1:]
                rows.append((coeffs, b))
    return rows


# ----------------------
# one-step FME
# ----------------------
def fme_eliminate_one(ineqs, var_index, cap=None):
    pos = []
    neg = []
    zero = []
    for a, b in ineqs:
        c = a[var_index]
        if c > 0:
            f = c
            pos.append(([v / f for v in a], b / f))
        elif c < 0:
            f = -c
            neg.append(([v / f for v in a], b / f))
        else:
            zero.append((a[:], b))
    est = len(pos) * len(neg) + len(zero)
    if cap is not None and est > cap:
        return None, {
            "count_pos": len(pos),
            "count_neg": len(neg),
            "count_zero": len(zero),
            "estimated": est,
            "total_after": None,
            "aborted": True,
        }
    new = []
    # carry zeros (drop eliminated column)
    for a, b in zero:
        new.append((a[:var_index] + a[var_index + 1 :], b))
    # combine pos x neg
    for ap, bp in pos:
        for an, bn in neg:
            new_a = [ap[i] + an[i] for i in range(len(ap)) if i != var_index]
            new_b = bp + bn
            new.append((new_a, new_b))
    info = {
        "count_pos": len(pos),
        "count_neg": len(neg),
        "count_zero": len(zero),
        "estimated": est,
        "total_after": len(new),
    }
    return new, info


# ----------------------
# helper: counts for a current column
# ----------------------
def pos_neg_counts_for_var(ineqs, var_index):
    pos = neg = zero = 0
    for a, b in ineqs:
        c = a[var_index]
        if c > 0:
            pos += 1
        elif c < 0:
            neg += 1
        else:
            zero += 1
    return pos, neg, zero


# ----------------------
# runner supporting subset & greedy-subset
# ----------------------
def run_fme(ineqs, order_0based, greedy=False, cap=500000):
    """
    Run naive FME following an explicit elimination order.

    Parameters
    - ineqs: list of (coeffs: List[Fraction], rhs: Fraction)
    - list of original variable indices (0-based). Interpretation:
        * if greedy is False: exact elimination order (will be followed, skipping eliminated).
        * if greedy is True: treated as a set of original indices; at each step pick
          the index from this set that minimizes p * n (computed on the current system).
    - greedy: bool, selects interpretation above.
    - cap: integer cap for early abort.

    Returns:
    - dict with keys: aborted (bool), steps (list of per-step info), final_count (int), time_s (float if not aborted)
    """
    if not ineqs:
        return {"aborted": False, "steps": [], "final_count": 0, "time_s": 0.0}
    if order_0based is None:
        raise ValueError(
            "elimination order (list of original indices, 0 based) must be provided"
        )
    n_vars = len(ineqs[0][0])
    current_vars = list(range(n_vars))  # maps current columns -> original indices
    cur = ineqs
    steps = []
    t_start = time.perf_counter()

    # Prepare depending on greedy flag
    if greedy:
        # treat input as a set of candidates to eliminate (remaining_subset)
        remaining_subset = list(
            dict.fromkeys(order_0based)
        )  # preserve order but unique
    else:
        # treat input as strict ordered list to follow
        ordered = list(order_0based)

    while True:
        # termination selection
        if greedy:
            # if no remaining items, done
            if not remaining_subset:
                break
            # choose best among remaining_subset that are still present
            best_pos = None
            best_prod = None
            best_orig = None
            # iterate a copy because we may remove elements
            for orig in list(remaining_subset):
                if orig not in current_vars:
                    # already eliminated earlier; remove from remaining set
                    remaining_subset.remove(orig)
                    continue
                pos_idx = current_vars.index(orig)
                p, n, z = pos_neg_counts_for_var(cur, pos_idx)
                prod = p * n
                if best_pos is None or prod < best_prod:
                    best_pos = pos_idx
                    best_prod = prod
                    best_orig = orig
            if best_pos is None:
                break
            pos = best_pos
            target_orig = best_orig
            # remove chosen original from remaining set
            remaining_subset.remove(target_orig)
        else:
            # exact-order mode
            if not ordered:
                break
            target_orig = ordered.pop(0)
            if target_orig not in current_vars:
                # skip if already eliminated earlier
                continue
            pos = current_vars.index(target_orig)

        # perform elimination at current column pos
        t0 = time.perf_counter()
        new, info = fme_eliminate_one(cur, pos, cap=cap)
        t1 = time.perf_counter()
        info["time_s"] = t1 - t0
        info["var_eliminated_original_index"] = target_orig
        info["var_eliminated_current_pos"] = pos

        if new is None:
            info.setdefault("aborted_by_cap", True)
            steps.append(info)
            elapsed = time.perf_counter() - t_start
            return {
                "aborted": True,
                "steps": steps,
                "final_count": info.get("estimated"),
                "time_s": elapsed,
            }

        info["total_after"] = len(new)
        steps.append(info)

        # defensive cap check
        if "estimated" in info and cap is not None and info["estimated"] > cap:
            elapsed = time.perf_counter() - t_start
            return {
                "aborted": True,
                "steps": steps,
                "final_count": info.get("estimated"),
                "time_s": elapsed,
            }

        # update mapping and current system
        del current_vars[pos]
        cur = new

    total = time.perf_counter() - t_start
    return {"aborted": False, "steps": steps, "final_count": len(cur), "time_s": total}


# ----------------------
# CLI
# ----------------------
if __name__ == "__main__":
    p = argparse.ArgumentParser(
        description="Naive FME runner (explicit order / subset-greedy)."
    )
    p.add_argument(
        "--input", type=Path, required=True, help="Path to cdd .ine file (H-format)"
    )
    p.add_argument(
        "--order",
        type=str,
        required=True,
        help="comma-separated list of 1-based original variable indices to eliminate (e.g. '8,3,1'). "
        "When --greedy is set, this list is treated as the candidate set for runtime greedy selection.",
    )
    p.add_argument(
        "--greedy",
        action="store_true",
        help="If set, treat --order as a candidate set and pick at each step the var minimizing pos*neg on the current system.",
    )
    p.add_argument(
        "--cap",
        type=int,
        default=500000,
        help="abort if estimated next-step exceeds this",
    )
    args = p.parse_args()

    ineqs = parse_ine_file(args.input)
    if not ineqs:
        raise SystemExit("No inequalities parsed from input.")

    # parse --order and --subset into 0-based original indices
    parts = [s.strip() for s in args.order.split(",") if s.strip()]
    try:
        order_0based = [int(x) - 1 for x in parts]
    except ValueError:
        raise SystemExit(
            "Invalid --order format: must be comma-separated integers (1-based)."
        )

    res = run_fme(
        ineqs,
        order_0based,
        greedy=args.greedy,
        cap=args.cap,
    )

    print("=== summary ===")
    print(json.dumps(res, indent=2, default=str))
