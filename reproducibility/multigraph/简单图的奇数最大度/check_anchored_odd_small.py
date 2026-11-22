"""Small odd degrees: enumerate slack vectors and solve exact old-template cover."""
import argparse
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations, product
from math import ceil, floor, isqrt

from check_anchored_odd_signature import exterior_capacity
from check_anchored_odd_threshold import GAMMA_C, EPSILON


def compositions(total, length):
    if length == 1:
        yield (total,)
    else:
        for j in range(total+1):
            for rest in compositions(total-j, length-1):
                yield (j,)+rest


def dihedral_representative(v):
    rev = v[::-1]
    return min(x[i:]+x[:i] for x in (v, rev) for i in range(5))


def covers_cycle(vertices):
    return all(i in vertices or (i+1)%5 in vertices for i in range(5))


def parts(d, s):
    amin = (d-sum(s))//2
    a = tuple(amin+s[(i-2)%5]+s[(i+2)%5] for i in range(5))
    assert all(d-a[(i-1)%5]-a[(i+1)%5] == s[i] for i in range(5))
    return a


class State:
    def __init__(self, d, slack, step):
        self.d, self.s, self.r, self.step = d, slack, sum(slack), step
        a = self.a = parts(d, slack)
        self.capacity = sum(x*y for x, y in zip(a, slack))
        self.support = {i for i in range(5) if slack[i]}
        self.no_exterior = not covers_cycle(self.support)
        covered_by_saturated_anchor = {(i-1)%5 for i in range(5) if not slack[i]}
        covered_by_saturated_anchor.update((i+1)%5 for i in range(5) if not slack[i])
        self.saturated_cover_parts = frozenset(covered_by_saturated_anchor)
        self.saturated_cover = sum(a[i] for i in covered_by_saturated_anchor)
        marked_capacity = sum(a[i]*slack[i] for i in self.support
                              if (i+2)%5 in self.support or (i+3)%5 in self.support)
        self.initial_m = ((2-self.r)*d-1-2*self.capacity+4*marked_capacity)//4-step
        self.smallest = min(a)
        self.forced = min(a[i]-slack[j] for i in range(5) for j in ((i-2)%5, (i+2)%5))
        self.adjacent_slack = max(slack[i]+slack[(i+1)%5] for i in range(5))
        self.cover_pieces = []
        for p in range(5):
            for pattern in product((False, True), repeat=4):
                selected = dict(zip([i for i in range(5) if i != p], pattern))
                x = [a[i] if selected.get(i, False) else 0 for i in range(5)]
                self.cover_pieces.append((sum(x), sum(x[i]*x[(i+1)%5] for i in range(5)),
                                          x[(p-1)%5]+x[(p+1)%5], a[p]))
        self.expansions = []
        limits = [range(min(slack[(i-1)%5], slack[(i+1)%5])+1) for i in range(5)]
        for counts in product(*limits):
            residual = tuple(slack[i]-counts[(i-1)%5]-counts[(i+1)%5] for i in range(5))
            if min(residual) < 0:
                continue
            rem = sum(residual)
            assert rem > 0 and rem%2
            expanded = tuple(a[i]+counts[i] for i in range(5))
            assert expand_check(d, residual, expanded)
            cap = sum(x*y for x, y in zip(residual, expanded))
            internal = sum(counts[i]*counts[(i+1)%5] for i in range(5))
            self.expansions.append((rem, cap, internal, residual, counts))
        self.expansions.sort()

    def cover(self, missing):
        largest = 0
        for n, cost, slope, size in self.cover_pieces:
            if cost <= missing:
                addition = min(size, (missing-cost)//slope) if slope else size
                largest = max(largest, n+addition)
        return max(sum(self.a)-largest, self.saturated_cover)

    def old_missing(self):
        initial = self.initial_m
        missing = initial+(0 if self.no_exterior else self.r*(self.d-1)//3)
        while missing >= 0:
            cover = self.cover(missing)
            if cover <= self.d:
                return {"reason": "cover", "missing": missing, "cover": cover}
            vertices = self.capacity//(cover-self.d)
            ext = 0 if self.no_exterior else min(vertices*(vertices-1)//2,
                      max(0, (vertices-1)*self.capacity//cover), max(0, (vertices-1)*self.r//3))
            next_missing = initial+ext
            if next_missing >= missing:
                break
            missing = next_missing
        return missing

    def cutoff(self, missing):
        for near in range(self.smallest, 0, -1):
            products = []
            for i, s in enumerate(self.s):
                j, k = (i+2)%5, (i+3)%5
                one, two = self.a[j]-near+1, self.a[k]-near+1
                products.append(min(one*max(two-s, 0), two*max(one-s, 0)))
            if min(products) > missing:
                return near
        return 0


def expand_check(d, s, a):
    return all(d-a[(i-1)%5]-a[(i+1)%5] == s[i] for i in range(5))


@lru_cache(maxsize=None)
def two_support_extras(a, b, s_a, s_b):
    """Maximum in the degree-and-anchor relaxation for two slack classes."""
    cap_a, cap_b = a*s_a, b*s_b
    types = set()
    for anchor_a, anchor_b in ((1, 0), (0, 1), (1, 1)):
        if anchor_a > s_a or anchor_b > s_b:
            continue
        for q_a in range(anchor_a, min(a, cap_a)+1):
            for q_b in range(anchor_b, min(b, cap_b)+1):
                if q_a == a and q_b == b:
                    continue
                p_a = 0
                p_b = 0
                if anchor_b and q_b >= b-(s_a-1):
                    p_a = q_a if q_b == b else min(q_a, s_b)
                if anchor_a and q_a >= a-(s_b-1):
                    p_b = q_b if q_a == a else min(q_b, s_a)
                if p_a+p_b:
                    types.add((q_a, q_b, anchor_a, anchor_b, p_a+p_b))
    # For any fixed anchor usage, Pareto-delete options spending at least as
    # many core slots while producing at most as many marks.
    active = [v for v in types if not any(
        u != v and u[2:4] == v[2:4] and u[0] <= v[0] and u[1] <= v[1] and u[4] >= v[4]
        for u in types)]

    @lru_cache(maxsize=None)
    def opt(left_a, left_b, available_a, available_b):
        best = min(left_a, left_b)
        for x, y, anchor_x, anchor_y, score in active:
            if x <= left_a and y <= left_b and anchor_x <= available_a and anchor_y <= available_b:
                best = max(best, score+opt(left_a-x, left_b-y,
                                           available_a-anchor_x, available_b-anchor_y))
        return best

    return opt(cap_a, cap_b, s_a, s_b)


def check_two_support(state):
    if len(state.support) != 2:
        return None
    i, j = sorted(state.support)
    if (i-j)%5 in (1, 4):
        return True
    a, b = state.a[i], state.a[j]
    s, r = state.s[i], state.s[j]
    assert a+b == state.d
    for k in range(min(s, r)+1):
        old_s, old_r = s-k, r-k
        rem = old_s+old_r
        if rem == 1:
            continue
        # Twice the difference F(D)-e_0 is (R-2)t+A+1/2.
        capacity = a*old_s+b*old_r
        target_times_four = (rem-2)*state.d+2*capacity+1
        extra = two_support_extras(a, b, old_s, old_r)
        if 4*extra > target_times_four-4+4*state.step:
            return False
    return True


@lru_cache(maxsize=None)
def anchor_profiles(slack):
    options = list(combinations(range(5), 3))
    options += [p for p in combinations(range(5), 2) if (p[0]-p[1])%5 in (2, 3)]
    possible = {(0, 0)}
    for group in options:
        if all(slack[i] for i in group):
            rest = tuple(x-(i in group) for i, x in enumerate(slack))
            possible.update((p+(len(group)==2), q+(len(group)==3))
                            for p, q in anchor_profiles(rest))
    return frozenset(possible)


def pure_weight_on_exact_rem_three(old_sizes, residual):
    candidates = []
    for j in range(5):
        for other in ((j-2)%5, (j+2)%5):
            if not residual[j] or not residual[other]:
                continue
            for i in ((j-2)%5, (j+2)%5):
                if residual[i] and other not in ((i+2)%5, (i+3)%5):
                    candidates.append(old_sizes[j]-(residual[i]-1)-residual[other])
    return min(candidates, default=0)


@lru_cache(maxsize=None)
def added_profiles(counts, residual):
    positions = [i for i, count in enumerate(counts) for _ in range(count)]
    possible = []

    def walk(depth, left, profile):
        if depth == len(positions):
            possible.append((tuple(profile), left))
            return
        i = positions[depth]
        choices = [j for j in (i, (i-2)%5, (i+2)%5) if left[j]]
        previous = profile[-1][1] if depth and profile[-1][0] == i else ()
        for qty in range(len(choices)+1):
            for extra in combinations(sorted(choices), qty):
                if extra < previous:
                    continue
                rest = tuple(x-(j in extra) for j, x in enumerate(left))
                walk(depth+1, rest, [*profile, (i, extra)])

    walk(0, residual, [])
    return tuple(possible)


def hole_bounds(old_sizes, old_slack, residual, profile, near, lo, hi):
    by_old_pair = [F(0)]*5
    open_directions = []
    for idx, (i, extra) in enumerate(profile):
        for direction in (-1, 1):
            target, opposite = (i+direction)%5, (i+2*direction)%5
            if opposite in extra:
                open_directions.append((idx, target, opposite, direction))
    absolute, unpriced = 0, 0
    for idx, target, opposite, direction in open_directions:
        i, extra = profile[idx]
        first = (i-direction)%5
        other_lost = sum(k != idx and j == first for k, j, _, _ in open_directions)
        wrong_first = min(old_slack[first], residual[first]+other_lost)
        first_cut = old_sizes[first] if (i-2*direction)%5 not in extra else near
        d = old_slack[i]+old_sizes[target]+old_sizes[first]
        wrong_new = d-first_cut-near-(len(extra)-1)
        gap = old_sizes[opposite]-wrong_new-wrong_first
        edge_index = target if direction == 1 else opposite
        cap = old_sizes[target]-near
        absolute += cap
        if gap > 0:
            by_old_pair[edge_index] += F(1, gap)
        else:
            unpriced += cap
    fee = max(by_old_pair)
    upper = min(floor(fee*hi)+unpriced, absolute)
    margin = max(lo-upper, ceil((1-fee)*(lo if fee<=1 else hi))-unpriced)
    return upper, margin, fee, unpriced


def one_range(state, lo, hi):
    d, slack, step = state.d, state.r, state.step
    cover = state.cover(hi)
    near = state.cutoff(hi)
    wrong = d-2*near
    normal_weight = min(near, cover-d, state.forced)
    if normal_weight <= 0:
        return {"reason": "cutoff/cover", "missing": (lo, hi), "cutoff": near, "cover": cover}
    for rem, cap, potential_new, residual, counts in state.expansions:
        count = (slack-rem)//2
        for profile, available in added_profiles(counts, residual):
            heavy = sum(bool(extra) for _, extra in profile)
            pure = count-heavy
            new_new_cap = min(potential_new, heavy*pure+heavy*(heavy-1)//2)
            anchor_slots = rem-sum(available)
            old_holes, old_margin, fee, unpriced = hole_bounds(
                state.a, state.s, residual, profile, near, lo, hi)
            if not old_holes:
                new_new_cap = 0
            else:
                new_new_cap = min(new_new_cap, (count-1)*old_holes)
            uncharged = 0 if 2*(near-wrong) >= slack else new_new_cap
            if rem == 1:
                assert anchor_slots <= 1
                if not heavy:
                    continue
                if state.smallest-state.adjacent_slack-old_holes >= 2-step:
                    uncharged = 0
                strict_old = (fee < 1 and unpriced == 0) or old_margin >= 1-step or old_holes == 0
                if not strict_old or (uncharged and old_margin < uncharged+1-step):
                    return {"reason": "completion holes", "added": profile,
                            "rem": rem, "missing": (lo, hi), "old_holes": old_holes,
                            "old_margin": old_margin, "new_new_cap": new_new_cap}
                continue
            weak_mark = min(state.adjacent_slack, count+rem-1)
            external_cover = covers_cycle({i for i in range(5) if available[i]})
            some_new_covers = any(covers_cycle({(i-1)%5, (i+1)%5, *extra})
                                  for i, extra in profile)
            witness = exterior_capacity(d, rem, anchor_slots, cap, old_holes+new_new_cap,
                                        cover, near, state.forced,
                                        normal_weight, max(state.forced-weak_mark, 0),
                                        max(near-weak_mark, 0), lo, old_margin-uncharged, step,
                                        exact_three_anchor_lemma=True,
                                        exact_three_pure_weight=pure_weight_on_exact_rem_three(state.a, residual),
                                        max_signature_size=len(state.support),
                                        no_exterior_edges=not external_cover,
                                        allowed_profiles=anchor_profiles(available),
                                        no_zero_anchor_endpoints=not external_cover and not some_new_covers)
            if witness is not None:
                return {"reason": "exterior capacity", "rem": rem, "added": profile,
                        "missing": (lo, hi), "cutoff": near, "cover": cover,
                        "cap": cap, "old_holes": old_holes, "old_margin": old_margin, **witness}
    return None


def one_degree(d, gamma_c, gamma_r, epsilon_c, epsilon_r, step, relax=False):
    deficit = F(2*d-1, 4)-step
    cycle = F(1, 8)-(deficit/d**2+epsilon_c)/gamma_c
    if cycle <= 0:
        return [{"reason": "no anchor existence"}]
    bound = floor((deficit/d+epsilon_r*d)/(gamma_r*cycle))
    failures = []
    if relax:
        from check_anchored_odd_relax import extra_bound, profile_extra_bound, target_diff

        def combined(state, lo, hi):
            witness = one_range(state, lo, hi)
            if witness is None:
                return None
            upper = extra_bound(state, hi)
            if upper <= target_diff(state)+state.step-1+lo:
                return None
            if lo == hi:
                target = target_diff(state)+state.step-1+lo
                paired_upper = profile_extra_bound(state, hi, target)
                if paired_upper <= target:
                    return None
                return {**witness, "relax_extra": upper, "paired_extra": paired_upper,
                        "relax_target": target}
            mid = (lo+hi)//2
            return combined(state, lo, mid) or combined(state, mid+1, hi)
    for r in range(3, bound+1, 2):
        for s in compositions(r, 5):
            if s != dihedral_representative(s):
                continue
            state = State(d, s, step)
            if state.smallest <= 0:
                # The anchor itself belongs to each old class.
                continue
            if check_two_support(state):
                continue
            missing = state.old_missing()
            if isinstance(missing, dict):
                if not relax:
                    failures.append({"slack": s, **missing})
                    continue
                missing = missing["missing"]
            if missing < 0 or one_range(state, 0, missing) is None:
                continue
            if relax:
                witness = combined(state, 0, missing)
                if witness is not None:
                    failures.append({"slack": s, **witness})
                continue
            for value in range(missing+1):
                witness = one_range(state, value, value)
                if witness is not None:
                    failures.append({"slack": s, **witness})
                    break
    return failures


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--start", type=int, default=9)
    parser.add_argument("--end", type=int, default=33)
    parser.add_argument("--anchor-gamma", type=F, default=F(54199, 100000))
    parser.add_argument("--anchor-epsilon", type=F, default=EPSILON)
    parser.add_argument("--abundance-gamma", type=F, default=GAMMA_C)
    parser.add_argument("--abundance-epsilon", type=F, default=EPSILON)
    parser.add_argument("--upper-bound-only", action="store_true")
    parser.add_argument("--samples", type=int, default=3)
    parser.add_argument("--relax", action="store_true")
    parser.add_argument("--require-complete", action="store_true")
    args = parser.parse_args()
    assert 3 <= args.start <= args.end and args.start%2 and args.end%2
    verified = []
    for d in range(args.start, args.end+1, 2):
        fail = one_degree(d, args.abundance_gamma, args.anchor_gamma,
                          args.abundance_epsilon, args.anchor_epsilon, int(args.upper_bound_only), args.relax)
        if not fail:
            verified.append(d)
        print({"degree": d, "unresolved_shapes": len(fail), "samples": fail[:args.samples]}, flush=True)
    print({"verified": verified, "exact_upper_only": args.upper_bound_only,
           "gamma_cycle": str(args.abundance_gamma), "gamma_anchor": str(args.anchor_gamma),
           "epsilon_cycle": str(args.abundance_epsilon), "epsilon_anchor": str(args.anchor_epsilon),
           "used_relaxation": args.relax},
          flush=True)
    if args.require_complete and len(verified) != (args.end-args.start)//2+1:
        raise SystemExit("At least one requested degree has an unresolved shape")


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run without -O/-OO or PYTHONOPTIMIZE")
    main()

