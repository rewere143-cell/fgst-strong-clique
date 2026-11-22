"""Find a Farkas certificate by minimizing violations of frozen Gram cuts."""
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
    parser.add_argument("--seconds", type=int, default=700)
    args = parser.parse_args()
    if args.vendor:
        sys.path.insert(0, str(args.vendor))
    import numpy as np
    from scipy.optimize import linprog
    from scipy.sparse import csr_matrix, hstack, vstack

    source = json.loads(args.start.read_bytes())
    settings = source["settings"]
    settings.pop("triangle_density_objective", None)
    system = build_system(settings)
    eq, iq, grams, sizes, _, _, scale, objective, _ = system
    cuts, directions = [], []
    for block, values in json.loads(args.directions.read_bytes()):
        vector = np.asarray(values, dtype=np.float64)
        assert 0 <= block < len(sizes) and vector.shape == (sizes[block],)
        directions.append((block, vector))
        cuts.append(csr_matrix(-((grams[block]/scale) @ np.outer(vector, vector).ravel())))
    D = vstack([iq / scale, *cuts], format="csr")
    slack = np.r_[np.zeros(iq.shape[0]), -np.ones(len(cuts))][:, None]
    augmented_ineq = hstack([D, csr_matrix(slack)], format="csr")
    augmented_eq = hstack([eq / scale, csr_matrix((eq.shape[0], 1))], format="csr")
    rhs = np.zeros(eq.shape[0])
    rhs[0] = 1
    result = linprog(np.r_[np.zeros(len(objective)), 1.0], A_eq=augmented_eq, b_eq=rhs,
                     A_ub=augmented_ineq, b_ub=np.zeros(D.shape[0]), bounds=(0,None),
                     method="highs-ipm", options={"time_limit": args.seconds})
    if not result.success or result.fun <= 0:
        print(json.dumps({"status": result.message, "violation": result.fun}), flush=True)
        raise SystemExit("No positive numerical violation bound.")
    print(json.dumps({"minimax_violation": float(result.fun)}), flush=True)
    ld, vd = source["linear_denominator"], source["vector_denominator"]
    multiplier = 1.0 / float(result.fun)
    candidate = dict(source, mode="infeasible")
    candidate["equalities"] = [round(-float(v)*ld*multiplier) for v in result.eqlin.marginals]
    dual = -result.ineqlin.marginals * multiplier
    candidate["inequalities"] = [max(0,round(float(v)*ld)) for v in dual[:iq.shape[0]]]
    candidate["gram_squared_vectors"] = [[] for _ in sizes]
    for mult, (block, vector) in zip(dual[iq.shape[0]:], directions):
        if mult > 0:
            factor = [round(float(x)*sqrt(mult)*vd) for x in vector]
            if any(factor):
                candidate["gram_squared_vectors"][block].append(factor)
    candidate["projection_inputs"] = verify_projection_inputs(settings)
    candidate["shadow_sha256"] = shadow_hashes(SHADOW)
    exact = verify(CACHE, candidate, system)
    print(json.dumps(exact, indent=2))
    if exact["rigorous_infeasible"] and F(exact["rational_bound"]) < 0:
        candidate["replay_result"] = exact
        args.output.write_text(json.dumps(candidate,separators=(",", ":"))+"\n", encoding="utf-8")
    else:
        raise SystemExit("The numerical violation did not yield a negative exact residual bound.")


if __name__ == "__main__":
    run()
