"""Exact scalar certificates for the coupled multigraph bipartite Ore bound."""

import argparse
from fractions import Fraction as Q
from time import monotonic

from check_multigraph_bipartite_twolevel import base_upper, harmonic, max_score, sqrt_interval
from check_multigraph_global_ore import check as verify_unrestricted_transfer


def one_level_table(beta, bins):
    ticks = [Q(j, bins) for j in range(bins+1)]
    table = []
    for i in range(bins):
        a0, a1 = ticks[i], ticks[i+1]
        base = base_upper(a0, a1)
        bmax = min(a1, 1-a0)
        upper = Q(0)
        for p0, p1 in zip(ticks[:i+1], ticks[1:i+2]):
            fcap = beta*(1-p0)**2
            theta = min(Q(1), p1/a0) if a0 else Q(1)
            upper = max(upper, base+max_score(fcap, theta, p1*bmax))
            if upper >= beta:
                upper = beta
                break
        table.append(upper)
    return table


def edge_score(x, ycap, own_cost, other_cost):
    """Upper bound for max_{0<=y<=ycap} harm(x,y)-own_cost*x-other_cost*y."""
    if other_cost*(x+ycap)**2 <= x*x:
        return harmonic(x, ycap) - own_cost*x - other_cost*ycap
    root_lo, _ = sqrt_interval(other_cost)
    return x*((1-root_lo)**2-own_cost)


def rectangle_score(tcap, fcap, theta, mu):
    if not tcap or not fcap or theta+mu <= 1:
        return Q(0)
    left_cost = mu*(1-theta)
    right_cost = theta*(1-mu)
    num = max(Q(0), edge_score(tcap, fcap, left_cost, right_cost),
              edge_score(fcap, tcap, right_cost, left_cost))
    return num/(theta*mu)


def verify(beta, bins, depth_limit):
    start = monotonic()
    table = one_level_table(beta, bins)
    print(f'Child envelope verified in {monotonic()-start:.2f}s', flush=True)
    unit = 1 << 20
    pending = [(0, unit, 0, unit, 0, unit, 0)]
    counts = dict(empty=0, first=0, one_level=0, coupled=0, split=0)
    max_depth = 0
    while pending:
        a0, a1, theta0, theta1, mu0, mu1, depth = pending.pop()
        max_depth = max(max_depth, depth)
        if theta1+mu1 <= unit or a0*(theta0+mu0) > unit*unit:
            counts['empty'] += 1
            continue
        a0, a1, theta0, theta1, mu0, mu1 = (Q(x, unit) for x in
                                            (a0, a1, theta0, theta1, mu0, mu1))
        p0, p1 = a0*theta0, a1*theta1
        base = base_upper(a0, a1)
        Tcap = p1*min(a1, 1-a0)
        if base+Tcap <= beta:
            counts['first'] += 1
            continue
        tauhi, taulo = 1-p0, 1-p1
        if base+max_score(beta*tauhi**2, theta1, Tcap) <= beta:
            counts['one_level'] += 1
            continue
        child_lo = min(bins-1, int(a0*mu0*bins/tauhi)) if tauhi else 0
        child_hi = min(bins-1, int(a1*mu1*bins/taulo)) if taulo else bins-1
        if child_hi < child_lo:
            raise ValueError('Bad residual maximum-degree range')
        Fcap = max(table[child_lo:child_hi+1])*tauhi**2
        if base+rectangle_score(Tcap, Fcap, theta1, mu1) <= beta:
            counts['coupled'] += 1
            continue
        points = [int(value*unit) for value in (a0, a1, theta0, theta1, mu0, mu1)]
        axis = max(range(0, 6, 2), key=lambda j: points[j+1]-points[j])
        if depth >= depth_limit or points[axis+1]-points[axis] < 2:
            raise ValueError(f'Unresolved box at depth {depth}: {points}')
        middle = (points[axis]+points[axis+1])//2
        left, right = points.copy(), points.copy()
        left[axis+1] = right[axis] = middle
        pending.extend(((*left, depth+1), (*right, depth+1)))
        counts['split'] += 1
    print(f'PASS beta={beta}, child grid {bins}: {counts}, '
          f'depth {max_depth}, elapsed {monotonic()-start:.2f}s')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--beta', type=Q, default=Q(2989, 10000))
    parser.add_argument('--child-bins', type=int, default=2048)
    parser.add_argument('--depth', type=int, default=58)
    args = parser.parse_args()
    verify(args.beta, args.child_bins, args.depth)
    verify_unrestricted_transfer(args.beta, 1+args.beta)
    if args.beta == Q(2989, 10000):
        verify_unrestricted_transfer(args.beta, Q(51, 40))
        epsilon = Q(3, 20000)
        assert Q(17, 20)-2*args.beta*Q(23, 20) > Q(4, 25)
        assert 1-2*args.beta-(1+2*args.beta)*Q(25, 2)*epsilon > 2/Q(502, 100)
        assert (1-Q(43, 20)*args.beta)/2 >= Q(1, 6)
        assert 1+args.beta-epsilon-Q(51, 40) > Q(1, 43)
        assert (43*Q(702, 100)+12)*epsilon < args.beta-Q(1, 4)-epsilon
        assert 1+args.beta-epsilon == Q(1039, 800)
        print('PASS re-rooting constants: maximum-degree coefficient 1039/800')

