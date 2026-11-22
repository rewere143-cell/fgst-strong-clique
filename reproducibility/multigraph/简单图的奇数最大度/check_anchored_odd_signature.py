"""Check sharpened odd-degree constants using anchor signatures."""
import argparse
from fractions import Fraction as F
from math import ceil, floor, isqrt

from check_anchored_odd_threshold import (
    EPSILON, GAMMA_R, OLD_THRESHOLD, anchor_slack_bound, old_core_bounds,
)


def exterior_capacity(d, rem, heavy_added, capacity, holes, cover, near_full, amin,
                      w_normal, w_pure, w_heavy, missing_min, hole_charge_min, deficit_step,
                      exact_three_anchor_lemma=False, exact_three_pure_weight=0,
                      max_signature_size=5, no_exterior_edges=False, allowed_profiles=None,
                      no_zero_anchor_endpoints=False):
    limit = capacity+2*holes
    slots = rem-heavy_added
    rich_cut = 2*near_full+amin+1
    exact_three = exact_three_anchor_lemma and rem == 3 and holes == 0
    exclude_heavy = exact_three or max_signature_size < 3
    exact_pure_core = exact_three and heavy_added == 0
    if exact_three:
        w_pure = max(w_pure, exact_three_pure_weight)
    for pure in range(slots//2+1):
        heavy_max = 0 if exclude_heavy else (slots-2*pure)//3
        for heavy in range(heavy_max+1):
            cut = pure*amin+2*heavy*near_full
            if cut > limit:
                continue
            rich_max = (min((slots-2*pure-3*heavy)//3, (limit-cut)//rich_cut)
                        if not exclude_heavy and max_signature_size > 3 and rich_cut <= d else 0)
            for rich in range(rich_max+1):
                if allowed_profiles is not None and (pure, heavy+rich) not in allowed_profiles:
                    continue
                normal_max = (limit-cut-rich*rich_cut)//w_normal
                if exact_pure_core or max_signature_size < 3 or no_zero_anchor_endpoints:
                    normal_max = min(normal_max, slots-2*pure)
                for normal in range(normal_max+1):
                    n = pure+heavy+rich+normal
                    weight = pure*w_pure+heavy*w_heavy+normal*w_normal
                    ext_edges = min(n*(n-1)//2, max(0, (n-1)*limit//cover),
                                    max(0, (n-1)*slots//3))
                    if no_exterior_edges:
                        ext_edges = 0
                    excess = min(d*n-2*weight-2*missing_min,
                                 capacity-2*weight+2*ext_edges-2*hole_charge_min)
                    if 2*excess > (rem-2)*d+3*deficit_step:
                        return {"pure": pure, "heavy": heavy, "rich": rich, "normal": normal,
                                "weight": weight, "excess": excess}
    return None


def one_missing_range(d, slack, lo, hi, cover, deficit_step):
    amin = (d-slack)//2
    near_full = amin-isqrt(hi)
    wrong = d-2*near_full
    pure_gap = amin-slack
    heavy_gap = amin-wrong
    if near_full <= slack:
        return {"reason": "prospective-clone conditions", "slack": slack, "near_full": near_full,
                "heavy_gap": heavy_gap, "missing": (lo, hi), "cover": cover}
    normal_weight = min(near_full, cover-d)
    assert pure_gap > 0 and normal_weight > 0
    for rem in range(1, slack+1, 2):
        count = (slack-rem)//2
        for multiple in range(min(rem//2, count)+1):
            for single in range(min(rem-2*multiple, count-multiple)+1):
                heavy = single+multiple
                pure = count-heavy
                new_new_cap = min(count**2//4, heavy*pure+heavy*(heavy-1)//2)
                multiplicity_slots = single+2*multiple
                single_gap = max(near_full-slack, near_full-count+3-rem-heavy)
                single_cap = single*((d+slack)//2-near_full)
                absolute_old_cap = single_cap+multiple*wrong
                if heavy_gap <= 0 and multiple:
                    # A zero old marking charge need not give a contradiction.
                    # Each clone still has at most b holes to its intended old parts.
                    old_holes = min(single_cap, single*hi//single_gap)+multiple*wrong
                    old_margin = lo-old_holes
                else:
                    old_fee = F(single, single_gap)+(F(multiple, heavy_gap) if multiple else 0)
                    old_holes = min(floor(old_fee*hi), absolute_old_cap)
                    old_margin = max(lo-old_holes, ceil((1-old_fee)*(lo if old_fee <= 1 else hi)))
                if old_holes == 0:
                    new_new_cap = 0
                else:
                    new_new_cap = min(new_new_cap, (count-1)*old_holes)
                uncharged = new_new_cap
                if 2*(near_full-wrong) >= slack:
                    uncharged = 0
                if rem == 1:
                    assert multiple == 0 and single <= 1
                    if single == 0:
                        continue
                    if pure_gap-old_holes >= 2:
                        uncharged = 0
                    if ((single_gap <= 1 and hi > 0 and not deficit_step) or
                        (uncharged and old_margin < uncharged+1-deficit_step)):
                        return {"reason": "completion hole bound", "slack": slack, "rem": rem,
                                "count": count, "added_heavy": (single, multiple),
                                "old_holes": old_holes, "old_margin": old_margin,
                                "uncharged": uncharged, "missing": (lo, hi), "near_full": near_full}
                    continue
                holes = old_holes+new_new_cap
                cap = (d*rem-1)//2
                weak_mark = count+rem-1
                witness = exterior_capacity(d, rem, multiplicity_slots, cap, holes, cover, near_full, amin,
                                            normal_weight, amin-weak_mark, near_full-weak_mark, lo,
                                            old_margin-uncharged, deficit_step)
                if witness is not None:
                    return {"reason": "exterior capacity", "slack": slack, "rem": rem, "count": count,
                            "added_heavy": (single, multiple), "holes": holes, "missing": (lo, hi), **witness}
    return None


def one_degree(d, gamma_r, epsilon_r, deficit_step):
    bound = anchor_slack_bound(d, gamma_r, epsilon_r, deficit_step=deficit_step)
    if bound is None:
        return {"reason": "no cycle abundance"}
    for slack in range(3, bound+1, 2):
        previous = old_core_bounds(d, slack, deficit_step=deficit_step)
        if previous is None:
            return {"reason": "cover", "slack": slack}
        missing, cover = previous
        if one_missing_range(d, slack, 0, missing, cover, deficit_step) is None:
            continue
        amin = (d-slack)//2
        for root in range(isqrt(missing)+1):
            lo, hi = root**2, min((root+1)**2-1, missing)
            improved_cover = ceil(F(3*d-slack, 2)-F(hi, amin))
            witness = one_missing_range(d, slack, lo, hi, improved_cover, deficit_step)
            if witness is not None:
                return witness
    return None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--start", type=int, default=31)
    parser.add_argument("--end", type=int, default=OLD_THRESHOLD-1)
    parser.add_argument("--scan", action="store_true")
    parser.add_argument("--anchor-gamma", type=F, default=GAMMA_R)
    parser.add_argument("--anchor-epsilon", type=F, default=EPSILON)
    parser.add_argument("--upper-bound-only", action="store_true")
    args = parser.parse_args()
    assert args.start%2 and args.end%2 and 3 <= args.start <= args.end < OLD_THRESHOLD
    largest_fail = None
    for d in range(args.start, args.end+1, 2):
        witness = one_degree(d, args.anchor_gamma, args.anchor_epsilon, int(args.upper_bound_only))
        if witness is None:
            continue
        largest_fail = d
        print(d, witness, flush=True)
        if not args.scan:
            raise AssertionError(witness)
    print({"start": args.start, "end": args.end, "largest_failed_degree": largest_fail,
           "anchor_gamma": str(args.anchor_gamma), "anchor_epsilon": str(args.anchor_epsilon),
           "upper_bound_only": args.upper_bound_only},
          flush=True)


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run without -O/-OO or PYTHONOPTIMIZE")
    main()

