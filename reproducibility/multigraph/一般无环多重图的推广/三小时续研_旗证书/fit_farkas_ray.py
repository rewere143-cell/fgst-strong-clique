"""Obtain and exactly replay an infeasibility ray for frozen Gram cuts."""
import argparse
from fractions import Fraction as F
import json
from math import sqrt
from pathlib import Path
import sys

from half_anchor_flag import CACHE, verify_projection_inputs
from half_anchor_shadow import SHADOW, build_system, shadow_hashes
from multigraph_weighted_maxdeg_exact import verify


def run():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("start", type=Path)
    parser.add_argument("directions", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--vendor", type=Path)
    parser.add_argument("--seconds", type=int, default=540)
    args = parser.parse_args()
    if args.vendor:
        sys.path.insert(0, str(args.vendor))
    import highspy
    import numpy as np
    from scipy.sparse import csr_matrix, vstack

    source = json.loads(args.start.read_bytes())
    settings = source["settings"]
    settings.pop("triangle_density_objective", None)
    eq, iq, grams, sizes, data, tags, scale, objective, roots = build_system(settings)
    cuts, directions = [], []
    for block, values in json.loads(args.directions.read_bytes()):
        v = np.asarray(values, dtype=np.float64)
        assert 0 <= block < len(sizes) and v.shape == (sizes[block],)
        directions.append((block, v))
        cuts.append(csr_matrix(-((grams[block] / scale) @ np.outer(v, v).ravel())))
    A = vstack([eq / scale, iq / scale, *cuts], format="csr")
    neq, niq = eq.shape[0], iq.shape[0]
    rhs = np.zeros(A.shape[0])
    rhs[0] = 1
    low = rhs.copy()
    low[neq:] = -highspy.kHighsInf
    h = highspy.Highs()
    for key, value in (("threads", 1), ("solver", "simplex"),
                       ("time_limit", float(args.seconds)), ("output_flag", True)):
        assert h.setOptionValue(key, value) != highspy.HighsStatus.kError
    n = A.shape[1]
    status = h.addCols(n, np.zeros(n), np.zeros(n), np.full(n, highspy.kHighsInf), 0,
                       np.zeros(n + 1, dtype=np.int32), np.zeros(0, dtype=np.int32),
                       np.zeros(0, dtype=np.float64))
    assert status != highspy.HighsStatus.kError
    status = h.addRows(A.shape[0], low, rhs, A.nnz, A.indptr.astype(np.int32, copy=False),
                       A.indices.astype(np.int32, copy=False), A.data)
    assert status != highspy.HighsStatus.kError
    h.run()
    print(str(h.getModelStatus()), flush=True)
    status, present, ray = h.getDualRay()
    if status == highspy.HighsStatus.kError or not present or not ray[0]:
        raise SystemExit("No numerical infeasibility ray returned.")
    cone = np.asarray(ray) * (-1.0/float(ray[0]))
    print(json.dumps({"max_absolute_ray_coefficient": float(np.max(abs(cone))),
                      "least_conic_multiplier": float(np.min(cone[neq:]))}), flush=True)
    ld, vd = source["linear_denominator"], source["vector_denominator"]
    candidate = dict(source, mode="infeasible")
    candidate["equalities"] = [round(float(v)*ld) for v in cone[:neq]]
    candidate["inequalities"] = [max(0, round(float(v)*ld)) for v in cone[neq:neq+niq]]
    candidate["gram_squared_vectors"] = [[] for _ in sizes]
    for mult, (block, vector) in zip(cone[neq+niq:], directions):
        if mult > 0:
            factor = [round(float(x)*sqrt(mult)*vd) for x in vector]
            if any(factor):
                candidate["gram_squared_vectors"][block].append(factor)
    candidate["projection_inputs"] = verify_projection_inputs(settings)
    candidate["shadow_sha256"] = shadow_hashes(SHADOW)
    result = verify(CACHE, candidate, (eq, iq, grams, sizes, data, tags, scale, objective, roots))
    print(json.dumps(result, indent=2))
    if result["rigorous_infeasible"] and F(result["rational_bound"]) < 0:
        candidate["replay_result"] = result
        args.output.write_text(json.dumps(candidate,separators=(",", ":"))+"\n", encoding="utf-8")
    else:
        raise SystemExit("The numerical ray did not yield a negative exact residual bound.")


if __name__ == "__main__":
    run()
