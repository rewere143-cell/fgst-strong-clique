"""Verify a scalar inequality for bipartite marked cliques with multiplicity."""

import argparse
from fractions import Fraction
import json


def check(beta, grid):
    """Return counts for integer interval bisection over a, p, b."""
    scale = 1 << grid
    half = scale // 2
    numerator, denominator = beta.numerator, beta.denominator
    target = numerator * scale**2
    pending = [((0, 0, 0), (scale, scale, half), 0)]
    splits = 0
    max_depth = 0
    while pending:
        lo, hi, depth = pending.pop()
        a0, p0, b0 = lo
        a1, p1, b1 = hi
        # Feasible parameters satisfy p <= a, b <= a and a + b <= 1.
        a0 = max(a0, p0, b0)
        a1 = min(a1, scale - b0)
        p1 = min(p1, a1)
        b1 = min(b1, a1, scale - a0)
        if a0 > a1 or p0 > p1 or b0 > b1:
            continue

        closest = min(max(half, a0), a1)
        base = denominator * closest * (scale - closest)
        k_max = denominator * p1 * b1
        if base + k_max <= target:
            continue

        f_max = numerator * (scale - p0)**2
        # The discarded nonnegative term is (a - p) max(0, b - f/a).
        # Multiply the upper bound by denominator * scale**2 for comparison.
        debit_num = max(0, a0 - p1) * max(0, denominator * a0 * b0 - f_max)
        debit_den = max(1, a0)
        harmonic_den = f_max + k_max
        harmonic_num = f_max * k_max
        if not harmonic_den:
            harmonic_den = 1
        if (
            (base - target) * debit_den * harmonic_den
            - debit_num * harmonic_den + harmonic_num * debit_den <= 0
        ):
            continue

        lo, hi = (a0, p0, b0), (a1, p1, b1)
        axis = max(range(3), key=lambda i: hi[i] - lo[i])
        if hi[axis] - lo[axis] <= 1:
            raise RuntimeError(f"unresolved integer interval {lo}, {hi} at scale {scale}")
        mid = (lo[axis] + hi[axis]) // 2
        right_lo, left_hi = list(lo), list(hi)
        right_lo[axis], left_hi[axis] = mid, mid
        pending.extend(((lo, tuple(left_hi), depth + 1), (tuple(right_lo), hi, depth + 1)))
        splits += 1
        max_depth = max(max_depth, depth + 1)
    return {"beta": str(beta), "integer_scale": scale, "splits": splits,
            "max_depth": max_depth, "unresolved": 0}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--beta", type=Fraction, default=Fraction(620, 1987))
    parser.add_argument("--grid", type=int, default=34)
    args = parser.parse_args()
    assert args.grid > 0 and args.beta > 0
    print(json.dumps(check(args.beta, args.grid), indent=2))


if __name__ == "__main__":
    main()
