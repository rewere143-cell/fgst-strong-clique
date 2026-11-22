"""Exact small arithmetic checks for the D9 parallel-mark reduction."""

from functools import cache
from itertools import product

from d7_bipartite_ore_coupled import bound, max_product


def triangle_rows(cost, q):
    """Allowed maximum Y2/Y3-to-Y0 marked degree if there is a Y0 point."""
    return tuple(
        r for r in range(1, 8)
        if q*r + 20 - 9*(cost+q) >= 0
        and max((r+2)//3, r-3)*(r+4-q) <= q*r + 20 - 9*(cost+q)
    )


@cache
def local_ore_rows(minimum=82, pi_w=7, degree=8):
    """Relaxed coupled Ore states for cross degree eight or nine and q=12."""
    states = []
    q, sigma = 12, 17
    for side, degree_host, count in product(
        range(2), range(degree, 10), range((degree+2)//3, degree+1),
    ):
        if side == 0 and degree_host > 8:
            continue
        neighbor_cap = min((9, 8)[side], sigma-degree_host)
        next_q = q-(1 if side == 0 else count)
        for remainder_degree in range(1, degree+1):
            remainder_cap = bound(8, 9, sigma-count, remainder_degree, next_q, 3)
            points = q-1 if side == 0 else remainder_cap
            for remainder in range(remainder_degree, remainder_cap+1):
                pi_cap = count*neighbor_cap-degree
                if side == 1:
                    pi_cap = min(pi_cap, pi_w)
                for unmarked in range(pi_cap+1):
                    incident = min(count*degree, count*neighbor_cap-unmarked)
                    total = incident+degree*(degree_host-degree)+remainder
                    if total < minimum:
                        continue
                    weighted = max_product(degree, remainder_degree, min(points, remainder),
                                           incident-degree, remainder, 3*count)
                    if count*remainder <= remainder_degree*unmarked+weighted:
                        states.append((side, degree_host, count, remainder_degree,
                                       remainder, unmarked, incident, total))
    return tuple(states)


def main():
    cross = tuple(bound(8, 9, 17, degree, 11, 3) for degree in range(1, 10))
    expected = (11, 22, 33, 44, 55, 66, 77, 83, 80)
    if cross != expected:
        raise ValueError((cross, expected))
    if any(triangle_rows(1, q) for q in range(1, 6)):
        raise ValueError("A triangle with a positive spoke loss survives")
    zero = {q: triangle_rows(0, q) for q in range(1, 9)}
    if zero != {1: (1, 2, 3, 4, 5), 2: (1, 2, 3),
                3: (), 4: (), 5: (), 6: (), 7: (), 8: ()}:
        raise ValueError(zero)
    cross12 = tuple(bound(8, 9, 17, degree, 12, 3) for degree in range(1, 10))
    if cross12 != (12, 24, 36, 48, 60, 72, 84, 83, 81):
        raise ValueError(cross12)
    states = local_ore_rows()
    expected_states = (
        (0, 8, 8, 5, 18, 8, 64, 82),
        (0, 8, 8, 5, 19, 9, 63, 82),
        (0, 8, 8, 5, 20, 10, 62, 82),
        (0, 8, 8, 5, 21, 11, 61, 82),
        (0, 8, 8, 5, 22, 12, 60, 82),
        (0, 8, 8, 6, 18, 6, 64, 82),
        (0, 8, 8, 6, 18, 7, 64, 82),
        (0, 8, 8, 6, 18, 8, 64, 82),
        (0, 8, 8, 6, 19, 7, 64, 83),
        (0, 8, 8, 6, 19, 8, 64, 83),
        (0, 8, 8, 6, 19, 9, 63, 82),
        (1, 9, 8, 6, 15, 5, 59, 82),
        (1, 9, 8, 6, 16, 6, 58, 82),
        (1, 9, 8, 6, 17, 7, 57, 82),
        (1, 9, 8, 6, 18, 7, 57, 83),
        (1, 9, 8, 7, 14, 4, 60, 82),
    )
    if states != expected_states:
        raise ValueError(states)
    for cross_count, w in product(range(82, 85), range(12, 15)):
        least_bits = 4 if cross_count == 84 else 3
        most_unmarked = cross_count-82
        for bits in range(least_bits, 7):
            lower = 14*bits*(w-7)-14*most_unmarked
            upper = w*(w-1)+(bits-1)*(9*w-cross_count)
            if lower <= upper:
                raise ValueError((cross_count, w, bits, lower, upper))
    print("q=11 cross bounds:", cross)
    print("Triangle zero-class integer bounds:", zero)
    print("q=12 cross bounds:", cross12)
    print("q=12 local cross states:", states)


if __name__ == "__main__":
    main()
