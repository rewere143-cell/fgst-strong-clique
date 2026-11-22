"""Replay a sixth-order certificate while checking sparse integer arithmetic."""
import argparse
from fractions import Fraction as F
import json
from pathlib import Path
import sys

from half_anchor_shadow import (CACHE, SHADOW, build_system, shadow_hashes,
                                verify, verify_projection_inputs)


def install_sparse_guards():
    import numpy as np
    from scipy.sparse import issparse
    from scipy.sparse._base import _spbase
    from scipy.sparse._data import _data_matrix

    statistics = {"sums": 0, "products": 0, "largest_bound": 0}

    def maximum(matrix):
        values = matrix.data
        return max(abs(int(values.min())), abs(int(values.max()))) if values.size else 0

    def check(item, bound, count):
        assert bound <= np.iinfo(item.dtype).max, (item.dtype, bound)
        statistics[count] += 1
        statistics["largest_bound"] = max(statistics["largest_bound"], bound)

    def guard_sum(original):
        def guarded(a, b):
            out = original(a, b)
            if (issparse(out) and issparse(b) and a.dtype.kind in "iu"
                    and b.dtype.kind in "iu" and out.dtype.kind in "iu"):
                check(out, maximum(a)+maximum(b), "sums")
            return out
        return guarded

    scalar_product = _data_matrix._mul_scalar

    def guarded_product(a, value):
        out = scalar_product(a, value)
        if a.dtype.kind in "iu" and isinstance(value, (int, np.integer)):
            check(out, maximum(a)*abs(int(value)), "products")
        return out

    _data_matrix._mul_scalar = guarded_product
    _spbase.__add__ = guard_sum(_spbase.__add__)
    _spbase.__sub__ = guard_sum(_spbase.__sub__)
    return statistics


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("--vendor", type=Path)
    args = parser.parse_args()
    if args.vendor:
        sys.path.insert(0, str(args.vendor))
    record = json.loads(args.certificate.read_bytes())
    settings = record["settings"]
    assert record["shadow_sha256"] == shadow_hashes(SHADOW)
    assert record["projection_inputs"] == verify_projection_inputs(settings)
    stats = install_sparse_guards()
    result = verify(CACHE, record, build_system(settings))
    assert F(result["rational_bound"]) == F(record["replay_result"]["rational_bound"])
    print(json.dumps(dict(statistics=stats, result=result), indent=2), flush=True)


if __name__ == "__main__":
    main()
