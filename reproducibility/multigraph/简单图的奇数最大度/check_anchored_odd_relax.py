"""Integer relaxation on outside anchor signatures and old-core capacities."""
import argparse
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import floor

from check_anchored_odd_small import State, compositions, covers_cycle, dihedral_representative

VERTICES = set(range(5))
OPPOSITE = [((i+2)%5, (i+3)%5) for i in range(5)]


def selected(mask):
    return tuple(i for i in range(5) if mask & (1<<i))


def allowed_masks(slack):
    return tuple(mask for mask in range(1, 32) if all(slack[i] for i in selected(mask)))


def after(slack, mask):
    return tuple(x-((mask>>i)&1) for i, x in enumerate(slack))


@lru_cache(maxsize=None)
def partner_limit(slack, own):
    return max((1+partner_limit(after(slack, mask), own) for mask in allowed_masks(slack)
                if covers_cycle(selected(mask|own))), default=0)


def minimum_product(u, v, extra):
    return min(u*max(v-extra, 0), v*max(u-extra, 0))


def max_mark_degree(state, host, signature, missing):
    """Upper bound on marked old-core degree for this host profile."""
    hs = set(selected(signature))
    a, slack = state.a, state.s
    p = [0]*5
    for i, q in enumerate(host):
        if not q:
            continue
        j, k = OPPOSITE[i]
        hits = [v for v in (j, k) if v in hs]
        if not hits:
            continue
        u, v = a[j]-host[j], a[k]-host[k]
        if len(hits) == 1:
            anchor_group = hits[0]
            misses = a[anchor_group]-host[anchor_group]
            if misses > slack[i]-1:
                continue
            p[i] = min(q-(i in hs), slack[anchor_group]) if misses else q
        else:
            if minimum_product(u, v, slack[i]-1) > missing:
                continue
            p[i] = q-((i in hs) and u*v>missing)
            if u*v > missing:
                # A remaining old marked edge has both ends outside N(x).
                # Every marked neighbor in U_i must use an extra host link
                # to one of its endpoints.
                p[i] = min(p[i], slack[j]+slack[k])
    if len(hs) == 2 and any(j in hs for i in hs for j in OPPOSITE[i]):
        # At most one of these two anchor adjacencies is marked. If an
        # unmarked anchor can be replaced by a marked neighbor of x without
        # losing an old type, the chosen anchor was not maximal.
        i, j = sorted(hs)
        best = 0
        for marked in (None, i, j):
            counts = p.copy()
            for a_index in (i, j):
                if marked != a_index:
                    counts[a_index] = min(counts[a_index], host[a_index]-1)
                if marked is not None and marked != a_index and slack[a_index] == 1:
                    counts[a_index] = min(counts[a_index], missing)
            if slack[i] == slack[j] == 1:
                best = max(best, sum(counts)-max(0, min(counts[i], counts[j])-missing))
            else:
                best = max(best, sum(counts))
        return best
    return sum(p)


def options_by_host_degree(state, missing, cover, scale):
    opts = {}
    for mask in allowed_masks(state.s):
        hs = set(selected(mask))
        max_core_marks = marks_by_total_degree(state, mask, missing)
        partner = partner_limit(after(state.s, mask), mask)
        zero_ok = covers_cycle(hs)
        cost_score = {}
        for q, p in max_core_marks.items():
            limit = state.d-q
            zeros = range(limit+1) if zero_ok and q+state.d>=cover else range(1)
            for zero in zeros:
                nonzero = min(partner, limit-zero) if q+state.d>=cover else 0
                cost = scale*q+zero*max(cover-q, 0)
                score = 2*p+2*zero+nonzero
                if score:
                    cost_score[cost] = max(cost_score.get(cost, 0), score)
        best = 0
        for cost, score in sorted(cost_score.items()):
            if score <= best:
                continue
            best = score
            opts.setdefault(mask, []).append((cost, score))
    return opts


def host_profiles(state, mask, missing):
    hs = set(selected(mask))
    bounds = [range(int(i in hs), state.a[i]-int(i not in hs)+1) if state.s[i]
              else range(1) for i in range(5)]
    for host in product(*bounds):
        q = sum(host)
        if q <= state.d:
            yield host, q, max_mark_degree(state, host, mask, missing)


def marks_by_total_degree(state, mask, missing):
    maximum = {}
    for _, q, p in host_profiles(state, mask, missing):
        maximum[q] = max(maximum.get(q, 0), p)
    return maximum


def zero_partners_bound(slack):
    """Maximum number of outside vertices each seeing a cycle cover."""
    return partner_limit(slack, 0)


def internal_wrong_marker_bound(state):
    edges = [(i, j) for i in state.support for j in state.support
             if i < j and j in OPPOSITE[i]]
    return min(sum(state.a[i]*state.s[i] for i in selected(mask))
               for mask in range(32) if all(mask & ((1<<i)|(1<<j)) for i, j in edges))


def extra_bound(state, missing):
    cover = state.cover(missing)
    scale = max(1, zero_partners_bound(state.s))
    options = options_by_host_degree(state, missing, cover, scale)
    p_cap = internal_wrong_marker_bound(state)
    w = scale*state.capacity

    @lru_cache(maxsize=None)
    def best(slots, left):
        answer = 2*min(left//(2*scale), p_cap)
        for sig in allowed_masks(slots):
            if sig not in options:
                continue
            rest = after(slots, sig)
            for cost, score in options[sig]:
                if cost <= left:
                    answer = max(answer, score+best(rest, left-cost))
        return answer

    return best(state.s, w)//2


@lru_cache(maxsize=None)
def signature_multisets(slack, first=1):
    outputs = [()]
    for mask in allowed_masks(slack):
        if mask >= first:
            outputs.extend((mask, *rest) for rest in signature_multisets(after(slack, mask), mask))
    return tuple(outputs)


@lru_cache(maxsize=None)
def paired_degrees(profile):
    edges = [(i, j) for i, x in enumerate(profile) for j, y in enumerate(profile[:i])
             if covers_cycle(selected(x|y))]
    degree_sequences = {(0,)*len(profile)}
    for i, j in edges:
        degree_sequences |= {tuple(h+(a==i)+(a==j) for a, h in enumerate(degree))
                             for degree in degree_sequences}
    return tuple(sorted(degree_sequences, key=sum, reverse=True))


def edge_sets_with_degrees(profile, target):
    edges = [(i, j) for i, x in enumerate(profile) for j, y in enumerate(profile[:i])
             if target[i] and target[j] and covers_cycle(selected(x|y))]

    def walk(index, degrees, chosen):
        if not any(degrees):
            yield chosen
            return
        if index == len(edges):
            return
        i, j = edges[index]
        if degrees[i] and degrees[j]:
            reduced = tuple(x-(k==i)-(k==j) for k, x in enumerate(degrees))
            yield from walk(index+1, reduced, (*chosen, (i, j)))
        yield from walk(index+1, degrees, chosen)

    yield from walk(0, target, ())


def profile_extra_bound(state, missing, abort_above):
    """Upper bound after selecting exact nonzero signatures and paired degrees."""
    cover, p_cap = state.cover(missing), internal_wrong_marker_bound(state)
    hosts = {mask: tuple(host_profiles(state, mask, missing)) for mask in allowed_masks(state.s)}
    tables = {}
    for mask, rows in hosts.items():
        table = tables[mask] = {}
        for _, q, p in rows:
            table[q] = max(table.get(q, 0), p)

    @lru_cache(maxsize=None)
    def options(mask, degree, scale):
        local = {}
        for q, p in tables[mask].items():
            if q+degree>state.d or (degree and q+state.d<cover):
                continue
            zeros = (range(state.d-q-degree+1) if covers_cycle(selected(mask)) and q+state.d>=cover
                     else range(1))
            for zero in zeros:
                cost = scale*q+zero*max(cover-q, 0)
                gain = p+zero
                local[cost] = max(local.get(cost, 0), gain)
        best, ans = -1, []
        for cost, gain in sorted(local.items()):
            if gain > best:
                ans.append((cost, gain))
                best = gain
        return tuple(ans)

    @lru_cache(maxsize=None)
    def best(group, left, scale):
        if not group:
            return min(left//(2*scale), p_cap)
        mask, degree = group[0]
        return max((gain+best(group[1:], left-cost, scale) for cost, gain in options(mask, degree, scale)
                    if cost<=left), default=-10**6)

    required_parts = state.saturated_cover_parts
    cover_sets = {mask: tuple(set(selected(z)) for z in range(32)
                              if z&mask==z and covers_cycle(selected(z))) for mask in hosts}
    irregular = [(i, j) for i in state.support for j in state.support if i<j and j in OPPOSITE[i]]
    covers_irregular = [tuple(selected(z)) for z in range(32)
                        if all(z&((1<<i)|(1<<j)) for i, j in irregular)]

    @lru_cache(maxsize=None)
    def zero_reserve(mask, q_i):
        q = sum(q_i)
        basic = tuple(state.a[i]-q_i[i] if i in required_parts else 0 for i in range(5))
        if missing:
            return max(cover-q, sum(basic)), basic
        choices = []
        for visit in cover_sets[mask]:
            needed = tuple(state.a[i]-q_i[i] if i in visit or i in required_parts else 0
                           for i in range(5))
            if all(needed[i] <= (state.a[i]-1 if state.s[i] else 0) for i in range(5)):
                choices.append(needed)
        if not choices:
            return state.d+1, basic
        return (max(cover-q, min(map(sum, choices))),
                tuple(min(row[i] for row in choices) for i in range(5)))

    @lru_cache(maxsize=None)
    def detailed_options(mask, degree, scale):
        permitted_zero = covers_cycle(selected(mask))
        out = []
        for host, q, p in hosts[mask]:
            if q+degree>state.d or (degree and q+state.d<cover):
                continue
            zero_q, zero_v = zero_reserve(mask, host) if permitted_zero else (state.d+1, (0,)*5)
            zeros = state.d-q-degree if zero_q<=state.d else 0
            for z in range(zeros+1):
                cost = scale*q+z*zero_q
                vector = tuple(scale*host[i]+z*zero_v[i] for i in range(5))
                if all(vector[i]<=scale*state.a[i]*state.s[i] for i in range(5)):
                    out.append((p+z, cost, vector, host))
        return tuple(sorted(set(out), key=lambda x:(x[1]-2*scale*x[0], x[1])))

    def pair_possible(mask, host, other_mask, other_host):
        if any(host[i]+other_host[i]<state.a[i] for i in required_parts):
            return False
        unseen = [max(state.a[i]-host[i]-other_host[i], int(not ((mask|other_mask)>>i&1)))
                  for i in range(5)]
        return sum(unseen[i]*unseen[(i+1)%5] for i in range(5)) <= missing

    def detailed(profile, degrees, scale, target):
        answer = 0
        local = [detailed_options(mask, degree, scale) for mask, degree in zip(profile, degrees)]
        order = tuple(sorted(range(len(profile)), key=lambda j:len(local[j])))
        suffix = [tuple(sorted((profile[j], degrees[j]) for j in order[t:]))
                  for t in range(len(order)+1)]
        caps = tuple(scale*state.a[i]*state.s[i] for i in range(5))
        selected_host = [None]*len(profile)
        for edges in edge_sets_with_degrees(profile, degrees):
            links = [{i for i in range(len(profile)) if (i,j) in edges or (j,i) in edges}
                     for j in range(len(profile))]

            def walk(index, gain, left, vector):
                nonlocal answer
                if index == len(order):
                    terminal = min(left//(2*scale),
                                   min(sum(vector[i]//scale for i in c) for c in covers_irregular))
                    answer = max(answer, gain+terminal+len(edges))
                    return answer>target
                if gain+best(suffix[index], left, scale)+len(edges)<=target:
                    return False
                j = order[index]
                for extra, cost, cons, host in local[j]:
                    if cost>left or any(cons[i]>vector[i] for i in range(5)):
                        continue
                    if gain+extra+best(suffix[index+1], left-cost, scale)+len(edges)<=target:
                        continue
                    if any(selected_host[k] is not None and
                           not pair_possible(profile[j], host, profile[k], selected_host[k]) for k in links[j]):
                        continue
                    selected_host[j] = host
                    hit = walk(index+1, gain+extra, left-cost,
                               tuple(vector[i]-cons[i] for i in range(5)))
                    selected_host[j] = None
                    if hit:
                        return True
                return False

            if walk(0, 0, scale*state.capacity, caps):
                return answer
        return min(target, answer)

    upper = 0
    for profile in signature_multisets(state.s):
        scale = max(1, sum(covers_cycle(selected(mask)) for mask in profile))
        for local_degrees in paired_degrees(profile):
            group = tuple(sorted(zip(profile, local_degrees)))
            result = best(group, scale*state.capacity, scale)+sum(local_degrees)//2
            if result > abort_above:
                result = detailed(profile, local_degrees, scale, abort_above)
            if result > upper:
                upper = result
            if upper > abort_above:
                return upper
    return upper


def target_diff(state):
    return ((state.r-2)*state.d+2*state.capacity+1)//4


def examine(state):
    possible = state.old_missing()
    if isinstance(possible, dict):
        possible = state.initial_m+(0 if state.no_exterior else state.r*(state.d-1)//3)
    objective = target_diff(state)+state.step-1
    attempts = 0

    def test(lo, hi):
        nonlocal attempts
        attempts += 1
        upper = extra_bound(state, hi)
        if upper <= objective+lo:
            return None
        if lo == hi:
            return (lo, upper, objective+lo)
        mid = (lo+hi)//2
        return test(lo, mid) or test(mid+1, hi)

    failure = test(0, possible) if possible>=0 else None
    return failure, attempts


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("degree", type=int)
    parser.add_argument("--slack", type=lambda v: tuple(map(int, v.split(","))))
    parser.add_argument("--max-slack", type=int, default=7)
    parser.add_argument("--upper-bound-only", action="store_true")
    args = parser.parse_args()
    assert args.degree%2 == 1
    unresolved, served = [], 0
    if args.slack is not None:
        shapes = [args.slack]
    else:
        shapes = [s for r in range(3, args.max_slack+1, 2) for s in compositions(r, 5)
                  if s == dihedral_representative(s)]
    for s in shapes:
        state = State(args.degree, s, int(args.upper_bound_only))
        if state.smallest<=0:
            continue
        failure, cases = examine(state)
        served += cases
        if failure is not None:
            unresolved.append((s, failure))
        print({"d": args.degree, "slack": s, "failure": failure, "cases": cases}, flush=True)
    print({"d": args.degree, "unresolved": unresolved, "cases": served}, flush=True)


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run without -O/-OO or PYTHONOPTIMIZE")
    main()

