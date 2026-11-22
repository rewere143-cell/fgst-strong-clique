"""Check all finite constants for the induced-cycle anchored odd-degree proof."""
import argparse
from fractions import Fraction as F
from math import ceil, floor, isqrt

GAMMA_C = F(6449, 10_000)
GAMMA_R = F(19734, 100_000)
EPSILON = F(1, 10**9)
OLD_THRESHOLD = 50_000


def anchor_slack_bound(d, gamma_r=GAMMA_R, epsilon_r=EPSILON, deficit_step=0):
    """Largest possible odd R for an anchor guaranteed by the exact duals."""
    deficit = F(2*d-1, 4)-deficit_step
    q = F(1, 8) - (deficit / d**2 + EPSILON) / GAMMA_C
    if q <= 0:
        return None
    mean = (deficit / d + epsilon_r*d) / (gamma_r*q)
    return (floor(mean) - 1) // 2 * 2 + 1


def old_core_bounds(d, slack, deficit_step=0):
    t = F(d, 2)
    base_min = (d-slack)//2
    if base_min <= 0:
        return None
    cap = (d*slack-1)//2
    missing = (d-1)//2-deficit_step+slack*(d-1)//3
    while True:
        cover = ceil(3*t - F(slack, 2) - F(missing, base_min))
        if cover <= d:
            return None
        n = cap // (cover-d)
        exterior_count = min(n*(n-1)//2, max(0, (n-1)*cap//cover),
                             max(0, (n-1)*slack//3))
        next_missing = (d-1)//2-deficit_step+exterior_count
        if next_missing >= missing:
            return missing, cover
        missing = next_missing


def compare_capacity(d, rem, capacity, holes, strong_weight, weak_weight, near_full,
                     cover, missing_min, hole_charge_min):
    """Eliminate R'≥3 by integer counts of the two exterior vertex types."""
    # With n total exterior endpoints, A'+2E bounds cut size, each endpoint
    # uses an unmarked quota, and each weak endpoint also uses 2*near_full.
    # The target doubled to an integer is (rem-2)*d.
    max_n = (capacity + 2*holes) // min(strong_weight, weak_weight)
    for n in range(max_n+1):
        ext_edges = min(n*(n-1)//2, max(0, (n-1)*(capacity+2*holes)//cover))
        for weak in range(n+1):
            weight = weak*weak_weight + (n-weak)*strong_weight
            cut_min = 2*near_full*weak + (n-weak)*strong_weight
            if cut_min > capacity+2*holes:
                continue
            excess_upper = min(d*n - 2*weight - 2*missing_min,
                               capacity - 2*weight + 2*ext_edges - 2*hole_charge_min)
            if 2*excess_upper > (rem-2)*d:
                return {"n": n, "weak": weak, "weight": weight, "excess": excess_upper}
    return None


def one_missing_range(d, slack, missing_min, missing_max, cover):
    amin = (d-slack)//2
    near_full = amin - isqrt(missing_max)
    wrong = d - 2*near_full
    old_gap = amin - wrong
    new_mark_gap = near_full - wrong
    if near_full <= slack or old_gap <= 0:
        return {"reason": "prospective-clone conditions", "slack": slack, "near_full": near_full,
                "old_gap": old_gap, "missing": (missing_min, missing_max), "cover": cover}
    weak_weight = near_full - slack
    strong_weight = min(near_full, cover-d)
    for rem in range(1, slack+1, 2):
        count = (slack-rem)//2
        new_new_holes = count**2//4
        hole_charge_min = ceil(F((old_gap-count)*missing_min, old_gap))
        if count >= 2 and 2*new_mark_gap < slack:
            hole_charge_min -= new_new_holes
            new_new_charged = hole_charge_min > 0
        else:
            new_new_charged = True
        if count >= old_gap or not new_new_charged:
            return {"reason": "completion hole bound", "slack": slack, "rem": rem, "count": count,
                    "old_gap": old_gap, "new_mark_gap": new_mark_gap, "missing": (missing_min, missing_max),
                    "near_full": near_full}
        if rem == 1:
            continue
        holes = (count*missing_max)//old_gap + new_new_holes
        capacity = (d*rem-1)//2
        witness = compare_capacity(d, rem, capacity, holes, strong_weight, weak_weight, near_full,
                                   cover, missing_min, hole_charge_min)
        if witness is not None:
            return {"reason": "outside capacity", "slack": slack, "rem": rem, "count": count,
                    "weak_weight": weak_weight, "strong_weight": strong_weight, "holes": holes,
                    "missing": (missing_min, missing_max), **witness}
    return None


def one_degree(d, gamma_r=GAMMA_R, epsilon_r=EPSILON):
    r_bound = anchor_slack_bound(d, gamma_r, epsilon_r)
    if r_bound is None:
        return {"reason": "no cycle abundance"}
    for slack in range(3, r_bound+1, 2):
        old = old_core_bounds(d, slack)
        if old is None:
            return {"reason": "cover", "slack": slack}
        missing, cover = old
        witness = one_missing_range(d, slack, 0, missing, cover)
        if witness is None:
            continue
        amin = (d-slack)//2
        for root in range(isqrt(missing)+1):
            lo, hi = root**2, min((root+1)**2-1, missing)
            better_cover = ceil(F(3*d-slack, 2) - F(hi, amin))
            witness = one_missing_range(d, slack, lo, hi, better_cover)
            if witness is not None:
                return witness
    return None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--start", type=int, default=101)
    parser.add_argument("--end", type=int, default=OLD_THRESHOLD-1)
    parser.add_argument("--scan", action="store_true", help="Report every small failed constant case.")
    parser.add_argument("--anchor-gamma", type=F, default=GAMMA_R)
    parser.add_argument("--anchor-epsilon", type=F, default=EPSILON)
    args = parser.parse_args()
    assert args.start % 2 and args.end % 2 and 3 <= args.start <= args.end < OLD_THRESHOLD
    largest_fail = None
    for d in range(args.start, args.end+1, 2):
        result = one_degree(d, args.anchor_gamma, args.anchor_epsilon)
        if result is None:
            continue
        largest_fail = d
        print(d, result, flush=True)
        if not args.scan:
            raise AssertionError(result)
    print({"start": args.start, "end": args.end, "largest_failed_degree": largest_fail,
           "anchor_gamma": str(args.anchor_gamma), "anchor_epsilon": str(args.anchor_epsilon)},
          flush=True)


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run without -O/-OO or PYTHONOPTIMIZE")
    main()

