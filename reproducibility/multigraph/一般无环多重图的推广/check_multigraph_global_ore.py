"""Exact dyadic tests of the scalar root bounds outside p,q >= 17/20."""
from fractions import Fraction

unit = 2**18
unit_square = unit * unit


def check(c_bound, target):
    pending = [(0, unit, 0, unit, 0, unit, 0, unit, 0)]
    counts = {"empty": 0, "first": 0, "second": 0, "monotone": 0, "split": 0}
    max_depth = 0
    c_num, c_den = c_bound.numerator, c_bound.denominator
    target_num, target_den = target.numerator, target.denominator
    while pending:
        a0, a1, b0, b1, p0, p1, q0, q1, depth = pending.pop()
        max_depth = max(max_depth, depth)

        # Intersect with b<=a, p<=a, q<=b by tightening coordinate bounds.
        b0 = max(b0, q0)
        a0 = max(a0, b0, p0)
        b1, p1 = min(b1, a1), min(p1, a1)
        q1 = min(q1, b1)
        if min(a1 - a0, b1 - b0, p1 - p0, q1 - q0) < 0:
            counts["empty"] += 1
            continue
        if min(p0, q0) * 20 >= 17 * unit:
            counts["monotone"] += 1
            continue

        upper_x = (a1 * (2 * unit - a1) + p1 * q1
                   - max(0, a0 - p1) * max(0, b0 - q1))
        if target_den * upper_x <= target_num * unit_square:
            counts["first"] += 1
            continue

        a_nearest_half = max(a0, min(a1, unit // 2))
        cap_h1 = min(c_num * (2 * unit - q0)**2,
                     c_den * (p1*b1 + a_nearest_half*(unit-a_nearest_half)))
        cap_h2 = c_num * (2 * unit - p0)**2
        upper_second = c_den * upper_x + cap_h1 + cap_h2
        if target_den * upper_second <= 2 * target_num * c_den * unit_square:
            counts["second"] += 1
            continue

        tightened = [a0, a1, b0, b1, p0, p1, q0, q1]
        split = max(range(0, 8, 2), key=lambda i: tightened[i+1]-tightened[i])
        assert tightened[split+1]-tightened[split] >= 2, tightened
        mid = (tightened[split]+tightened[split+1])//2
        left, right = tightened.copy(), tightened.copy()
        left[split+1], right[split] = mid, mid
        pending.extend([(*left, depth+1), (*right, depth+1)])
        counts["split"] += 1

    lower = Fraction(17, 20)
    assert lower - 2 * c_bound * (2 - lower) > 0
    print("Exact certificate: c =", c_bound, "target =", target,
          counts, "maximum subdivision depth", max_depth)


if __name__ == "__main__":
    assert (Fraction(7, 4) - Fraction(43, 128))**2 < 2
    check(Fraction(43, 128), Fraction(4, 3))
    check(Fraction(1, 3), Fraction(1333, 1000))
    check(Fraction(1, 3), Fraction(33, 25))
