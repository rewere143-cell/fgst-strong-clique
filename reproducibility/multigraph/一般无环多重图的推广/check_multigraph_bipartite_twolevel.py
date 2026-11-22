"""Exact rational checker for the two-level marked-bipartite Ore bound."""

import argparse
from fractions import Fraction as Q
from math import isqrt
from time import monotonic


def harmonic(a, b):
    return a*b/(a+b) if a and b else Q(0)


def base_upper(a0, a1):
    a = max(a0, min(a1, Q(1, 2)))
    return a*(1-a)


def sqrt_interval(x, scale=1 << 15):
    lower = isqrt(x.numerator*scale*scale // x.denominator)
    return Q(lower, scale), Q(lower+1, scale)


def child_box(a0, a1, p0, p1, coefficient):
    """Upper bound over the child's actual a, p and all feasible b."""
    bmax = min(a1, 1-a0)
    y = coefficient*(1-p0)**2
    k = max(Q(0), a0-p1)
    knee = min(bmax, y/a0) if a0 else bmax
    if not y or not p1 or knee == bmax:
        return harmonic(p1*bmax, y)
    # b -> harm(p1*b,y) - k*(b-knee)_+ is concave.
    derivative_numerator = p1*y*y
    if derivative_numerator <= k*(p1*knee+y)**2:
        return harmonic(p1*knee, y)
    if derivative_numerator >= k*(p1*bmax+y)**2:
        return harmonic(p1*bmax, y)-k*(bmax-knee)
    root0, root1 = sqrt_interval(p1/k)
    low = max(knee, min(bmax, y*(root0-1)/p1))
    high = max(knee, min(bmax, y*(root1-1)/p1))
    return harmonic(p1*high, y)-k*(low-knee)


def child_table(coefficient, bins):
    ticks = [Q(i, bins) for i in range(bins+1)]
    table = []
    for i in range(bins):
        a0, a1 = ticks[i], ticks[i+1]
        base = base_upper(a0, a1)
        upper = Q(0)
        for j in range(i+1):
            p0, p1 = ticks[j], ticks[j+1]
            upper = max(upper, base + child_box(a0, a1, p0, p1, coefficient))
            if upper >= coefficient:
                upper = coefficient
                break
        table.append(upper)
    return table


def max_score(H, mu, cap):
    if not H or not mu or not cap:
        return Q(0)
    if mu*(H+cap)**2 >= (H+cap)**2-H**2:
        return cap - (cap*cap)/(mu*(H+cap))
    root, _ = sqrt_interval(1-mu)
    return H*(1-root)/(1+root)


def verify(coefficient, bins, depth_limit):
    started = monotonic()
    table = child_table(coefficient, bins)
    print(f'Child envelope verified in {monotonic()-started:.2f}s', flush=True)
    unit = 1 << 20
    zero, one = 0, unit
    pending = [(zero, one, zero, one, zero, one, zero, one, 0)]
    counts = {'empty': 0, 'first': 0, 'one_level': 0, 'two_level': 0, 'split': 0}
    max_depth = 0
    while pending:
        a0, a1, p0, p1, b0, b1, v0, v1, depth = pending.pop()
        max_depth = max(max_depth, depth)
        a0 = max(a0, p0, b0, v0)
        a1 = min(a1, unit-b0)
        p1 = min(p1, a1, unit-v0)
        b1 = min(b1, a1, unit-a0)
        v1 = min(v1, a1, unit-p0)
        if min(a1-a0, p1-p0, b1-b0, v1-v0) < 0:
            counts['empty'] += 1
            continue

        nearest_half = max(a0, min(a1, unit//2))
        base = Q(nearest_half*(unit-nearest_half), unit*unit)
        H = Q(p1*b1, unit*unit)
        if base+H <= coefficient:
            counts['first'] += 1
            continue

        tau_hi, tau_lo = unit-p0, unit-p1
        # First-level KMP bound applies also when the true v is zero.
        parent_cap = coefficient*Q(tau_hi*tau_hi, unit*unit)
        loose_penalty = (
            Q(max(0, a0-p1), unit)
            * max(Q(0), Q(b0, unit) - parent_cap*unit/a0)
        ) if a0 else Q(0)
        if base+harmonic(H, parent_cap)-loose_penalty <= coefficient:
            counts['one_level'] += 1
            continue

        child_low = min(bins-1, v0*bins//tau_hi) if tau_hi else 0
        child_high = min(bins-1, v1*bins//tau_lo) if tau_lo else bins-1
        if child_low > child_high:
            raise ValueError('Bad range of residual maximum degree')
        cap = max(table[child_low:child_high+1])*Q(tau_hi*tau_hi, unit*unit)
        mu = min(Q(1), Q(v1, a0)) if a0 else Q(1)
        penalty = (
            Q(max(0,a0-p1), unit)
            * max(Q(0), Q(b0, unit)-cap*unit/v0)
        ) if v0 else Q(0)
        if base+max_score(H, mu, cap)-penalty <= coefficient:
            counts['two_level'] += 1
            continue

        endpoints = [a0, a1, p0, p1, b0, b1, v0, v1]
        axis = max(range(0, 8, 2), key=lambda i: endpoints[i+1]-endpoints[i])
        if depth == depth_limit or endpoints[axis+1]-endpoints[axis] < 2:
            raise ValueError(f'Unresolved parent box at depth {depth}: {endpoints}')
        midpoint = (endpoints[axis]+endpoints[axis+1])//2
        left, right = endpoints.copy(), endpoints.copy()
        left[axis+1] = right[axis] = midpoint
        pending.extend(((*left, depth+1), (*right, depth+1)))
        counts['split'] += 1
        if counts['split'] % 100000 == 0:
            print(f'{counts["split"]} exact splits; {monotonic()-started:.1f}s', flush=True)

    print(f'PASS beta={coefficient}, child grid {bins}: {counts}, '
          f'maximum depth {max_depth}, elapsed {monotonic()-started:.2f}s')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--beta', type=Q, default=Q(31, 100))
    parser.add_argument('--child-bins', type=int, default=256)
    parser.add_argument('--depth', type=int, default=58)
    args = parser.parse_args()
    verify(args.beta, args.child_bins, args.depth)

