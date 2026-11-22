"""Refine valid conditional Ore tables using the residual degree ratio as a coordinate."""

import argparse
from fractions import Fraction as Q
import json
from pathlib import Path
import sys
from time import monotonic

from check_multigraph_bipartite_coupled import rectangle_score
from check_multigraph_bipartite_twolevel import base_upper, max_score


def exact_test(profile, a_interval, target, limit, depth_limit=56):
    if base_upper(*a_interval) > target:
        return False, 0, 0
    bins = len(profile)
    pending = [(a_interval, (Q(0), Q(1)), (0, bins-1), 0)]
    branches = 0
    deepest = 0
    cached = {}
    while pending:
        a, theta, child, depth = pending.pop()
        deepest = max(deepest, depth)
        al, ah = a
        thl, thh = theta
        i, j = child
        cl, ch = Q(i, bins), Q(j+1, bins)
        taul, tauh = 1-ah*thh, 1-al*thl
        if cl*taul > ah:
            continue
        mu = min(Q(1), ch*tauh/al) if al else Q(1)
        if thh+mu <= 1:
            continue
        arep = max(al, min(ah, Q(1, 2)))
        base = arep*(1-arep)
        tcap = thh*arep*min(arep, 1-arep)
        if base+tcap <= target:
            continue
        if child not in cached:
            cached[child] = max(profile[i:j+1])
        fcap = min(cached[child]*tauh**2, min(ah, ch*tauh)*(1-al))
        if base+max_score(fcap, thh, tcap) <= target:
            continue
        if base+rectangle_score(tcap, fcap, thh, mu) <= target:
            continue
        branches += 1
        if branches > limit or depth >= depth_limit:
            return False, branches, deepest
        axis = max(range(3), key=lambda k: (
            ah-al, thh-thl, Q(j-i, bins)
        )[k])
        if axis == 2:
            if i == j:
                return False, branches, deepest
            mid = (i+j)//2
            pending.extend(((a, theta, (i, mid), depth+1), (a, theta, (mid+1, j), depth+1)))
        elif axis == 1:
            mid = (thl+thh)/2
            pending.extend(((a, (thl, mid), child, depth+1), (a, (mid, thh), child, depth+1)))
        else:
            mid = (al+ah)/2
            pending.extend((((al, mid), theta, child, depth+1), ((mid, ah), theta, child, depth+1)))
    return True, branches, deepest


def propose(profile, margin, theta_count):
    """Float candidates only; subsequent interval tests are the proof."""
    import numpy as np
    from scipy.optimize import minimize

    bins = len(profile)
    old = np.asarray(list(map(float, profile)))[None, None, :]
    c_upper = (np.arange(bins)+1)[None, None, :]/bins
    c_lower = c_upper-1/bins
    grid = np.linspace(0.01, 1., theta_count)
    margin = float(margin)

    def value(a, theta):
        a = np.asarray(a)
        theta = np.asarray(theta)
        p = a*theta
        tau = 1-p
        tcap = p*np.minimum(a, 1-a)
        u = np.minimum(a, c_upper*tau)
        mu = u/np.maximum(a, 1e-12)
        fcap = np.minimum(old*tau*tau, u*(1-a))
        left, right = mu*(1-theta), theta*(1-mu)
        denom = np.maximum(1e-12, tcap+fcap)
        endpoint = tcap*fcap/denom-left*tcap-right*fcap
        first = np.where(right <= (tcap/denom)**2, endpoint, tcap*((1-np.sqrt(right))**2-left))
        second = np.where(left <= (fcap/denom)**2, endpoint, fcap*((1-np.sqrt(left))**2-right))
        valid = (theta+mu > 1) & (c_lower*tau <= a)
        extra = np.where(valid, np.maximum(np.maximum(first, second), 0)/np.maximum(1e-12, theta*mu), 0)
        return a*(1-a)+np.max(extra, axis=2, keepdims=True)

    result = []
    for i, fallback in enumerate(profile):
        al, ah = i/bins, (i+1)/bins
        a_points = np.array([al, (al+ah)/2, ah])
        values = value(a_points[:, None, None], grid[None, :, None])[:, :, 0]
        best_points = np.argpartition(values.ravel(), -3)[-3:]
        best = float(values.max())
        for ai, ti in zip(*np.unravel_index(best_points, values.shape)):
            out = minimize(
                lambda v: -float(value(v[0], v[1]).item()), (a_points[ai], grid[ti]),
                method="Powell", bounds=((al, ah), (0.01, 1.)),
                options={"maxiter": 15, "xtol": 1e-6, "ftol": 1e-7},
            )
            best = max(best, -out.fun)
        proposed = Q(int(np.ceil((best+margin)*10**7)), 10**7)
        result.append(min(fallback, proposed))
    return result


def refine(profile, proposals, limit, printed=False):
    assert len(profile) == len(proposals)
    result = []
    stats = {"proved": 0, "fallback": 0, "branches": 0, "max_depth": 0}
    bins = len(profile)
    for i, proposed in enumerate(proposals):
        if proposed >= profile[i]:
            result.append(profile[i])
            continue
        proved, work, depth = exact_test(profile, (Q(i, bins), Q(i+1, bins)), proposed, limit)
        stats["proved" if proved else "fallback"] += 1
        stats["branches"] += work
        stats["max_depth"] = max(stats["max_depth"], depth)
        result.append(proposed if proved else profile[i])
        if printed and i % 64 == 0:
            print(f"Profile up to bin {i}: {stats}", flush=True)
    return result, stats


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("profile", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--vendor", type=Path)
    parser.add_argument("--target", type=Q)
    parser.add_argument("--rounds", type=int, default=2)
    parser.add_argument("--margin", type=Q, default=Q(1, 20000))
    parser.add_argument("--work-limit", type=int, default=6000)
    parser.add_argument("--theta-count", type=int, default=41)
    parser.add_argument("--replay", type=Path)
    args = parser.parse_args()
    if args.vendor:
        sys.path.insert(0, str(args.vendor))
    source = json.loads(args.profile.read_bytes())
    assert source["proved"]
    profile = [Q(x) for x in source["last_table"]]
    report = {"proved": True, "target": source["target"], "estimates": [], "stats": []}
    start = monotonic()
    proposals = json.loads(args.replay.read_bytes())["estimates"] if args.replay else None
    for i in range(len(proposals) if proposals is not None else args.rounds):
        row = list(map(Q, proposals[i])) if proposals is not None else propose(profile, args.margin, args.theta_count)
        profile, status = refine(profile, row, args.work_limit)
        report["estimates"].append(list(map(str, row)))
        report["stats"].append(status)
        report["last_table"] = list(map(str, profile))
        args.output.write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8")
        print(f"Round {i+1}: {status}, seconds {monotonic()-start:.1f}", flush=True)
    if args.target:
        proved, work, depth = exact_test(profile, (Q(0), Q(1)), args.target, 600000)
        report["root_check"] = dict(proved=proved, branches=work, depth=depth, target=str(args.target))
        print(report["root_check"], flush=True)
        if proved:
            report["target"] = str(args.target)
        args.output.write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8")


if __name__ == "__main__":
    main()
