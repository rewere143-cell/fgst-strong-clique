"""Exact interval use of the witness-defect and neighborhood-difference inequalities."""

import argparse
from fractions import Fraction as Q
import json
from math import isqrt
from pathlib import Path
from time import monotonic

from check_multigraph_bipartite_coupled import one_level_table
from check_multigraph_bipartite_profile import concave_score


UNIT = 1 << 24


def sqrt_hi(q, scale=1 << 24):
    if not q:
        return Q(0)
    n, d = q.numerator*scale*scale, q.denominator
    root = isqrt(n//d)
    if root*root*d < n:
        root += 1
    return Q(root, scale)


def rectangle(theta, mu, tl, th, fl, fh):
    if theta+mu <= 1 or not th or not fh:
        return Q(0)
    score = Q(0)
    left = max(tl, (1-mu)*fh/mu)
    right = min(th, theta*fh/(1-theta)) if theta < 1 else th
    if left <= right:
        score = max(score, concave_score(fh, Q(1), 1-mu*(1-theta), left, right)
                    -theta*(1-mu)*fh)
    left = max(fl, (1-theta)*th/theta)
    right = min(fh, mu*th/(1-mu)) if mu < 1 else fh
    if left <= right:
        score = max(score, concave_score(th, Q(1), 1-theta*(1-mu), left, right)
                    -mu*(1-theta)*th)
    return score/(theta*mu)


def rounded(q, ceil):
    return (q.numerator*UNIT+(q.denominator-1 if ceil else 0))//q.denominator


def witness_incompatible(a, p, u, b, f, t, delta, theta, parts, tight=False):
    al, ah = a
    pl, ph = p
    ul, uh = u
    fl, fh = f
    tl, th = t
    if min(al, tl, fl) <= 0:
        return False
    gamma_l, gamma_h = fl/(th+fl), fh/(tl+fh)
    alpha_l, alpha_h = 1-gamma_h, 1-gamma_l
    hlo, hhi = al*alpha_l, ah*alpha_h
    fstar_l, fstar_h = al*gamma_l, ah*gamma_h
    mark_gap, copy_gap = pl-hhi, ul-fstar_h
    if min(mark_gap, copy_gap) <= 0:
        return False
    error_factor = min(alpha_l**2, gamma_l**2)
    nmax = (th+fh)/al
    dup = min(2*hhi, 2*(ph-hlo))
    c0 = 1-pl-fstar_l-ul
    for part in range(parts):
        W = theta*uh*delta*Q(part+1, parts)
        S = theta*delta*Q(parts-part, parts)
        nmin = max(Q(0), (tl+fl)/ah-W/(al*al*gamma_l**2))
        ew = W/(al*error_factor)
        es = alpha_h*ew+sqrt_hi(nmax*W)+W*(4/(al*gamma_l)+16/(9*al*gamma_l**2))
        epi = 2*W/copy_gap+4*ph*W/copy_gap**2
        eg = sqrt_hi(2*nmax*W)+2*ew
        if tight:
            mark_loss = max(alpha_h/(al*error_factor), 2/(al*gamma_l), 1/(al*gamma_l**2))
            es = sqrt_hi(nmax*W)+mark_loss*W
            epi = W*min(max(1/((1-ratio)*copy_gap), ph/(ratio*copy_gap)**2)
                        for ratio in (Q(1, 2), Q(2, 3), Q(3, 4), Q(4, 5)))
            weighted_blue = W*min(
                max((ratio*uh+(1-ratio)*fstar_h)/((1-ratio)*copy_gap),
                    uh*ph/(ratio*copy_gap)**2)
                for ratio in (Q(1, 2), Q(2, 3), Q(3, 4), Q(4, 5))
            )
            y_linear = uh*ah*W
            y_constant = uh*(W+weighted_blue)
            y_loss = ((sqrt_hi(y_linear)+sqrt_hi(y_linear+4*mark_gap*y_constant))
                      /(2*mark_gap))**2
            one_sided = sqrt_hi(nmax*W)/2 + W*max(
                (alpha_h+Q(1, 2))/(al*error_factor), Q(1, 2)/(al*gamma_l),
                2/(al*gamma_l), 1/(al*gamma_l**2),
            )
            g_f = sqrt_hi(uh*fh*W)
            lower_weighted = (max(0, nmin-b)*max(0, hlo*fl-W)
                              - nmax*(g_f+fh*sqrt_hi(S/2)+weighted_blue)
                              - fh*(one_sided+epi))
            c_direct = 1-pl-fstar_l-ul
            upper_weighted = (max(c_direct*fl, c_direct*fh)+ah*gamma_h*ew
                              +g_f+weighted_blue+y_loss)
            if lower_weighted > (ph-hlo)*max(0, upper_weighted):
                continue
        lo = (2*max(0, nmin-b)*max(0, hlo*nmin-es)
              - 2*sqrt_hi(S/2)*nmax**2 - 4*nmax*epi - 2*nmax*es)
        if lo <= 0:
            return False
        hi = (max(c0*fl, c0*fh)+ah*(ew+es+epi)
              +uh*(W+ah*(es+epi))/mark_gap + nmax*eg)
        if fstar_l*lo > max(0, hi)*dup:
            continue

        # Use the same Ore count with s_x - w_x <= -f_x and
        # Cauchy--Schwarz in its two weighted error terms.
        lower = lo/dup
        if 4*fstar_l*fstar_l*lower < 2*nmax*W:
            return False
        boundary = (uh+fstar_h)/2
        if not tight:
            weighted_blue = 2*boundary*W/copy_gap+4*uh*ph*W/copy_gap**2
        coefficient = uh*ah*W
        constant = uh*(W+weighted_blue)
        y_loss = (
            (sqrt_hi(coefficient)+sqrt_hi(coefficient+4*mark_gap*constant))/(2*mark_gap)
        )**2
        budget = (max(c0*fl, c0*fh)+ah*(gamma_h*ew+sqrt_hi(nmax*W))
                  +weighted_blue+y_loss+2*nmax*ew)
        if fstar_l*lower-sqrt_hi(2*nmax*W*lower) <= budget:
            return False
    return True


def inspect(box, beta, prior_beta, profile, parts, tight=False):
    a0, a1, th0, th1, mu0, mu1, t0, t1, f0, f1 = (Q(x, UNIT) for x in box)
    if th1+mu1 <= 1 or a0*(th0+mu0) > 1:
        return "empty", box
    # Only points above a(1-a) can violate the desired coefficient.
    th0, mu0 = max(th0, 1-mu1), max(mu0, 1-th1)
    if th0+mu0:
        a1 = min(a1, 1/(th0+mu0))
    if a0:
        th1, mu1 = min(th1, 1/a0-mu0), min(mu1, 1/a0-th0)
    if a0 > a1 or th0 > th1 or mu0 > mu1:
        return "empty", box
    p0, p1 = a0*th0, a1*th1
    u0, u1 = a0*mu0, min(a1*mu1, 1-p0)
    aa = max(a0, min(a1, Q(1, 2)))
    base = aa*(1-aa)
    b = min(a1, 1-a0)
    t1 = min(t1, th1*aa*min(aa, 1-aa))
    if t0 > t1:
        return "empty", box
    if base+t1 <= beta:
        return "root", box
    tau0, tau1 = 1-p1, 1-p0
    f1 = min(f1, prior_beta*tau1*tau1, u1*(1-a0))
    if f0 > f1:
        return "empty", box
    bins = len(profile)
    child0 = min(bins-1, int(u0*bins/tau1)) if tau1 else 0
    child1 = min(bins-1, int(u1*bins/tau0)) if tau0 else bins-1
    if child0 > child1:
        return "empty", box
    f1 = min(f1, max(profile[child0:child1+1])*tau1**2)
    if f0 > f1:
        return "empty", box
    if t0*(1-th1) >= th1*f1 or f0*(1-mu1) >= mu1*t1:
        return "empty", box
    # Positive mass above the base requires both T and f.
    floor = max(Q(0), beta-base)*th0*mu0
    tl, fl = max(t0, floor), max(f0, floor)
    if tl > t1 or fl > f1:
        return "empty", box
    up = min(base+t1, base+rectangle(th1, mu1, tl, t1, fl, f1))
    if up <= beta:
        return "coupled", box
    # F and T near their upper bounds are the only difficult region.
    for _ in range(2):
        split_f = (fl+f1)/2
        if base+rectangle(th1, mu1, tl, t1, fl, split_f) <= beta:
            fl = split_f
        split_t = (tl+t1)/2
        if base+rectangle(th1, mu1, tl, split_t, fl, f1) <= beta:
            tl = split_t
    if witness_incompatible((a0, a1), (p0, p1), (u0, u1), b, (fl, f1),
                            (tl, t1), up-beta, th1, parts, tight):
        return "witness", box
    endpoints = (a0, a1, th0, th1, mu0, mu1, tl, t1, fl, f1)
    smaller = tuple(rounded(q, bool(i % 2)) for i, q in enumerate(endpoints))
    return "split", smaller


def verify(beta, prior_beta, bins, parts, max_splits, seconds, table_file=None, tight=False):
    start = monotonic()
    if table_file:
        previous = json.loads(table_file.read_bytes())
        assert previous["proved"] and prior_beta >= Q(previous["target"])
        profile = [Q(bound) for bound in previous["last_table"]]
    else:
        profile = one_level_table(prior_beta, bins)
    print(f"Exact child table assembled after {monotonic()-start:.2f}s", flush=True)
    pending = [((0, UNIT, 0, UNIT, 0, UNIT, 0, UNIT, 0, UNIT), 0)]
    counts = {k: 0 for k in ("empty", "root", "coupled", "witness", "split")}
    deepest = 0
    while pending:
        if counts["split"] >= max_splits or monotonic()-start >= seconds:
            raise RuntimeError(f"Search limit with {len(pending)} remaining boxes: {counts}")
        original, depth = pending.pop()
        deepest = max(deepest, depth)
        result, box = inspect(original, beta, prior_beta, profile, parts, tight)
        counts[result] += 1
        if result != "split":
            continue
        axis = max(range(0, 10, 2), key=lambda i: (
            (box[i+1]-box[i])*(1, 1, Q(1, 3), Q(1, 2), 2, 2)[i//2]
        ))
        if box[axis+1]-box[axis] <= 1:
            raise RuntimeError(f"Unresolved fine interval: {box}, counts {counts}")
        mid = (box[axis]+box[axis+1])//2
        left, right = list(box), list(box)
        left[axis+1] = right[axis] = mid
        pending.extend(((tuple(left), depth+1), (tuple(right), depth+1)))
        if counts["split"] % 10000 == 0:
            print(f"Splits={counts['split']}; time={monotonic()-start:.1f}; depth={deepest}; "
                  f"witness={counts['witness']}; pending={len(pending)}", flush=True)
    print(f"PASS beta={beta}, earlier beta={prior_beta}, counts={counts}, "
          f"depth={deepest}, seconds={monotonic()-start:.2f}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--beta", type=Q, default=Q(239, 800))
    parser.add_argument("--prior-beta", type=Q)
    parser.add_argument("--bins", type=int, default=2048)
    parser.add_argument("--parts", type=int, default=2)
    parser.add_argument("--splits", type=int, default=1500000)
    parser.add_argument("--seconds", type=int, default=1200)
    parser.add_argument("--conditional-table", type=Path)
    parser.add_argument("--tight", action="store_true")
    args = parser.parse_args()
    verify(args.beta, args.prior_beta or args.beta, args.bins, args.parts, args.splits,
           args.seconds, args.conditional_table, args.tight)
