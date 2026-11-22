"""Verify conditional Ore-degree bounds through repeated profile refinement."""

import argparse
from fractions import Fraction as Q
from time import monotonic

from check_multigraph_bipartite_twolevel import base_upper, child_table, harmonic, sqrt_interval


UNIT = 1 << 24


def normalize(box):
    a0, a1, p0, p1, b0, b1, v0, v1 = box
    a0 = max(a0, p0, b0, v0)
    a1 = min(a1, UNIT - b0)
    p1 = min(p1, a1, UNIT - v0)
    b1 = min(b1, a1, UNIT - a0)
    v1 = min(v1, a1, UNIT - p0)
    if min(a1 - a0, p1 - p0, b1 - b0, v1 - v0) < 0:
        return None
    return a0, a1, p0, p1, b0, b1, v0, v1


def concave_score(k, mu, slope, low, high):
    """Upper bound max_{low<=f<=high} slope*f - f^2/[mu(k+f)]."""
    if not k:
        return (slope - 1/mu) * (high if slope >= 1/mu else low)

    def value(f):
        return slope*f - f*f/(mu*(k+f))

    shift = 1 - mu*slope
    if shift*(k+high)**2 <= k*k:
        return value(high)
    if shift*(k+low)**2 >= k*k:
        return value(low)
    root, _ = sqrt_interval(shift, 1 << 23)
    return k*(1-root)**2/mu


def score_with_penalty(k, mu, cap, excess, b, v):
    if not mu or not cap:
        return -excess*b if v else Q(0)
    if not v or not excess or not b:
        return concave_score(k, mu, Q(1), Q(0), cap)
    turn = b*v
    left = concave_score(k, mu, 1+excess/v, Q(0), min(turn, cap))-excess*b
    if cap <= turn:
        return left
    return max(left, concave_score(k, mu, Q(1), turn, cap))

def coupled_score(theta, mu, t_cap, f_cap):
    """Bound the jointly charged witness score in the feasible rectangle."""
    score = Q(0)
    if not t_cap or not f_cap or theta+mu <= 1:
        return score

    t_lo = (1-mu)*f_cap/mu
    t_hi = min(t_cap, theta*f_cap/(1-theta)) if theta < 1 else t_cap
    if t_lo <= t_hi:
        fixed_f = concave_score(f_cap, Q(1), 1-mu*(1-theta), t_lo, t_hi)
        score = max(score, fixed_f-theta*(1-mu)*f_cap)

    f_lo = (1-theta)*t_cap/theta
    f_hi = min(f_cap, mu*t_cap/(1-mu)) if mu < 1 else f_cap
    if f_lo <= f_hi:
        fixed_t = concave_score(t_cap, Q(1), 1-theta*(1-mu), f_lo, f_hi)
        score = max(score, fixed_t-mu*(1-theta)*t_cap)

    return score/(theta*mu)


def initial_profile(beta, bins):
    profile = child_table(beta, bins)
    for i, previous in enumerate(profile):
        a0, a1 = Q(i, bins), Q(i+1, bins)
        base = base_upper(a0, a1)
        b_max = min(a1, 1-a0)
        upper = Q(0)
        for j in range(i+1):
            p0, p1 = Q(j, bins), Q(j+1, bins)
            t_cap = p1*b_max
            f_cap = beta*(1-p0)**2
            theta = min(Q(1), p1/a0) if a0 else Q(1)
            upper = max(upper, base+coupled_score(theta, Q(1), t_cap, f_cap))
            if upper >= previous:
                break
        profile[i] = min(previous, upper)
    return profile


def box_upper(box, profile, beta, cutoff):
    a0, a1, p0, p1, b0, b1, v0, v1 = box
    closest = max(a0, min(a1, UNIT//2))
    base = Q(closest*(UNIT-closest), UNIT**2)
    k = Q(p1*b1, UNIT**2)
    first = base+k
    if first <= cutoff:
        return first

    tau0, tau1 = UNIT-p1, UNIT-p0
    excess = Q(max(0, a0-p1), UNIT)
    b = Q(b0, UNIT)
    cap = beta*Q(tau1*tau1, UNIT**2)
    first_penalty = excess*max(Q(0), b-cap*UNIT/a0) if a0 else Q(0)
    first = min(first, base+harmonic(k, cap)-first_penalty)
    theta = min(Q(1), Q(p1, a0)) if a0 else Q(1)
    first = min(first, base+coupled_score(theta, Q(1), k, cap))
    if first <= cutoff:
        return first

    bins = len(profile)
    child_low = min(bins-1, v0*bins//tau1) if tau1 else 0
    child_high = min(bins-1, v1*bins//tau0) if tau0 else bins-1
    assert child_low <= child_high
    cap *= max(profile[child_low:child_high+1])/beta
    mu = min(Q(1), Q(v1, a0)) if a0 else Q(1)
    return min(
        first,
        base + score_with_penalty(k, mu, cap, excess, b, Q(v0, UNIT)),
        base + coupled_score(theta, mu, k, cap),
    )


def refine_box(initial, profile, beta, cutoff, max_depth, split_budget=None):
    pending = [(initial, 0)]
    upper = Q(0)
    splits = 0
    depth_max = 0
    while pending:
        box, depth = pending.pop()
        depth_max = max(depth_max, depth)
        box = normalize(box)
        if box is None:
            continue
        bound = box_upper(box, profile, beta, cutoff)
        if bound <= cutoff:
            upper = max(upper, bound)
            continue
        axis = max(range(0, 8, 2), key=lambda i: box[i+1]-box[i])
        if (depth >= max_depth or box[axis+1]-box[axis] <= 1
                or split_budget is not None and splits >= split_budget):
            upper = max(upper, bound)
            continue
        midpoint = (box[axis]+box[axis+1])//2
        left, right = list(box), list(box)
        left[axis+1] = right[axis] = midpoint
        pending.extend(((left, depth+1), (right, depth+1)))
        splits += 1
    return upper, splits, depth_max


def verify(beta, bins, iterations, profile_depth, profile_budget, proof_depth, margin):
    assert UNIT % bins == 0
    start = monotonic()
    profile = initial_profile(beta, bins)
    print(f"Built {bins} initial profile entries after {monotonic()-start:.2f}s", flush=True)
    for i in range(iterations):
        next_profile = []
        step = UNIT//bins
        changed = 0
        for j, old in enumerate(profile):
            if old < beta-Q(3, 100):
                next_profile.append(old)
                continue
            box = (j*step, (j+1)*step, 0, UNIT, 0, UNIT//2, 0, UNIT)
            bound, _, _ = refine_box(
                box, profile, beta, old-margin, profile_depth, profile_budget,
            )
            improved = min(old, bound)
            next_profile.append(improved)
            changed += int(improved < old)
        profile = next_profile
        print(
            f"Refinement {i+1}: tightened {changed} entries after {monotonic()-start:.2f}s",
            flush=True,
        )

    initial = (0, UNIT, 0, UNIT, 0, UNIT//2, 0, UNIT)
    upper, splits, depth = refine_box(initial, profile, beta, beta, proof_depth)
    print(f"beta={beta}; splits={splits}; maximum depth={depth}; upper={float(upper):.12f}; "
          f"verified={upper <= beta}; elapsed={monotonic()-start:.2f}s", flush=True)
    if upper > beta:
        raise RuntimeError("Root bound above requested coefficient")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--beta", type=Q, default=Q(77, 250))
    parser.add_argument("--bins", type=int, default=256)
    parser.add_argument("--iterations", type=int, default=1)
    parser.add_argument("--profile-depth", type=int, default=24)
    parser.add_argument("--profile-budget", type=int, default=600)
    parser.add_argument("--proof-depth", type=int, default=42)
    parser.add_argument("--margin", type=Q, default=Q(1, 1000))
    args = parser.parse_args()
    verify(args.beta, args.bins, args.iterations, args.profile_depth, args.profile_budget,
           args.proof_depth, args.margin)
