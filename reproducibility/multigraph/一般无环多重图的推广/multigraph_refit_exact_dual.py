"""Refit the linear multipliers of an existing rational weighted flag certificate."""

import argparse
import json
from pathlib import Path
import sys

from multigraph_weighted_maxdeg_exact import build_integer, verify


def repair(cache, original, seconds, expected_system=None):
    import numpy as np
    from scipy.optimize import linprog

    system = expected_system or build_integer(cache, original["settings"])
    eq, iq, matrices, sizes, _, _, scale, objective, _ = system
    vden = original["vector_denominator"]
    score = (objective/2).astype(np.float64) if original["mode"] == "bound" else np.zeros_like(objective, dtype=np.float64)
    for matrix, n, basis in zip(matrices, sizes, original["gram_squared_vectors"]):
        if not basis:
            continue
        v = np.asarray(basis, dtype=np.float64).reshape(-1, n)/vden
        score += matrix@((v.T@v).ravel()/scale)
    rhs = np.zeros(eq.shape[0])
    rhs[0] = 1.
    lp = linprog(-score, A_ub=iq/scale, b_ub=np.zeros(iq.shape[0]), A_eq=eq/scale, b_eq=rhs,
                 bounds=(0, None), method="highs-ipm", options={"time_limit": seconds})
    if not lp.success:
        raise RuntimeError(lp.message)
    lden = original["linear_denominator"]
    refined = dict(original)
    refined["equalities"] = [round(-float(x)*lden) for x in lp.eqlin.marginals]
    refined["inequalities"] = [max(0, round(-float(x)*lden)) for x in lp.ineqlin.marginals]
    result = verify(cache, refined, system)
    refined["replay_result"] = result
    return refined


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("cache", type=Path)
    parser.add_argument("source", type=Path)
    parser.add_argument("out", type=Path)
    parser.add_argument("--vendor", type=Path)
    parser.add_argument("--seconds", type=int, default=150)
    args = parser.parse_args()
    if args.vendor:
        sys.path.insert(0, str(args.vendor))
    original = json.loads(args.source.read_bytes())
    result = repair(args.cache, original, args.seconds)
    replay = result["replay_result"]
    print(json.dumps(replay, indent=2))
    if replay["decimal_bound"] < original["replay_result"]["decimal_bound"]:
        args.out.write_text(json.dumps(result, separators=(",", ":"))+"\n", encoding="utf-8")


if __name__ == "__main__":
    main()
