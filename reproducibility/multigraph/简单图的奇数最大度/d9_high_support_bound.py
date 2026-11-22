"""Integer bounds for high support orders in the degree-nine simple case."""

from collections import Counter
from functools import cache
from itertools import product
import json

from odd_fixed_degree_sat import profiles


@cache
def group_bounds(size, capacity, compulsory, outer):
    """Possible (outer vertex count, internal mark cap) for one inner part."""
    feasible = set()
    for full in range(compulsory, capacity + 1):
        remaining = capacity - full
        full_cap = full * (8 - size) - outer * compulsory
        if full_cap < 0:
            continue
        if size == 1 and remaining:
            continue
        partial_incidences = size * remaining
        for partial_vertices in range(partial_incidences + 1):
            if partial_incidences > (size - 1) * partial_vertices:
                continue
            partial_cap = 0
            if size >= 2:
                partial_cap = remaining**2
            if size >= 3:
                excess = partial_incidences - partial_vertices
                partial_cap = min(partial_cap, remaining * excess // (size - 2))
            feasible.add((full + partial_vertices, full_cap + partial_cap))
    return tuple(sorted(feasible))


def complete_bound(left, right):
    """Bound marked edges outside a saturated complete bipartite core."""
    a, b = 9 - right, 9 - left
    return max(a*a, a*(8-left)) + max(b*b, b*(8-right))


def possible_complete(saturated):
    for x in range(1, 10):
        for y in range(1, x + 1):
            isolates = saturated - x - y
            if isolates < 0 or x*y < 9*saturated-98:
                continue
            if isolates and x+y > 9:
                continue
            required_outside = 98-9*(x+y)+x*y
            if required_outside <= complete_bound(x, y):
                yield x, y, isolates


def possible_path(saturated, order, leaves):
    for x in range((saturated + 1)//2, 10):
        y = saturated - x
        if not 2 <= y <= x:
            continue
        alpha, beta = 9-x, 9-y
        for a1, a4 in product(range(1, x), range(1, y)):
            a2, a3 = y-a4, x-a1
            internal = 98 - 9*saturated + x*y - a1*a4
            if a1+a4 > 8 or internal < 0:
                continue
            for gamma in range(max(a1,a4), min(9-a2,9-a3)+1):
                c1, c4 = beta+a4-gamma, alpha+a1-gamma
                zero_cap = c1*max(0,8-x) + c4*max(0,8-y)
                leaf_cap = a2*(gamma-a1)+a3*(gamma-a4)+zero_cap
                if leaves > leaf_cap:
                    continue
                left = group_bounds(a2,alpha,c4,a4)
                right = group_bounds(a3,beta,c1,a1)
                for (ln, lj), (rn, rj) in product(left,right):
                    if lj+rj >= internal and saturated+gamma+ln+rn+min(internal,zero_cap) >= order:
                        yield a1,a2,a3,a4,gamma
                        break


def main():
    all_profiles = Counter()
    remaining = Counter()
    for order, _, degree_counts, _ in profiles(9):
        if order < 29:
            continue
        sat, leaves = degree_counts[-1], degree_counts[0]
        all_profiles[order, sat] += 1
        if sat <= 10 or any(possible_complete(sat)) or any(possible_path(sat,order,leaves)):
            remaining[order, sat] += 1
    assert max(order for order, _ in all_profiles) == 37
    assert not any(order >= 32 or sat >= 15 for order, sat in remaining)
    print(json.dumps({
        "starting_profiles": sum(all_profiles.values()),
        "remaining_profiles": sum(remaining.values()),
        "remaining_by_order_and_saturated": [
            {"order": order, "saturated": sat, "profiles": count}
            for (order, sat), count in sorted(remaining.items())
        ]
    }, indent=2))


if __name__ == "__main__":
    main()
