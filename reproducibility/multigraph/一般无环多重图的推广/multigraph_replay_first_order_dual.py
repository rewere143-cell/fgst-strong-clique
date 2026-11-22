"""Exactly verify a sparse obstruction to a forest-tagged lift family."""

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import sys

from multigraph_affine_lift_search import build


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("snapshot", type=Path)
    parser.add_argument("base_certificate", type=Path)
    parser.add_argument("dual_certificate", type=Path)
    parser.add_argument("--vendor", type=Path)
    args = parser.parse_args()
    if args.vendor:
        sys.path.insert(0, str(args.vendor))

    proof = json.loads(args.dual_certificate.read_bytes())
    assert proof["base_certificate_sha256"] == hashlib.sha256(
        args.base_certificate.read_bytes()
    ).hexdigest()
    _, _, _, _, _, _, tag_size, rhs, scale, restricted, matrix, objective = build(
        args.snapshot, args.base_certificate, face_only=False, boolean=False, profiles=True,
        monomials=True, multiplier_degree=1, test_degree=1, tagged_gram=proof["tagged_gram"],
    )
    assert tuple(proof["matrix_shape"]) == matrix.shape
    weights = {row: Fraction(value) for row, value in proof["weights"]}
    assert len(weights) == len(proof["weights"])
    assert all(0 <= row < matrix.shape[0] and tag_size[row] <= 1 for row in weights)
    assert all(value > 0 for value in weights.values())

    # If A x <= b and y >= 0, then -y^T b <= -y^T A x.
    # The column checks imply -y^T A x <= c^T x for every allowed x.
    column_sums = [Fraction(0) for _ in objective]
    numerator = Fraction(0)
    for row, weight in weights.items():
        numerator -= weight * int(rhs[row])
        start, end = matrix.indptr[row:row + 2]
        for column, coefficient in zip(matrix.indices[start:end], matrix.data[start:end]):
            column_sums[column] += weight * int(coefficient)
    for value, coefficient, nonnegative in zip(column_sums, objective, restricted):
        if nonnegative:
            assert value >= -int(coefficient)
        else:
            assert value == -int(coefficient)
    minimum_allowance = numerator / scale
    assert minimum_allowance == Fraction(proof["necessary_allowance"])
    assert minimum_allowance > Fraction(5, 4)
    print(json.dumps({
        "checked_columns": matrix.shape[1],
        "positive_dual_weights": len(weights),
        "necessary_allowance": str(minimum_allowance),
        "exceeds_five_quarters": True,
    }, indent=2))


if __name__ == "__main__":
    main()
