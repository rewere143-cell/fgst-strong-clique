"""Find and replay simple-support anchor inequalities for triangle-free marks."""

import argparse
from fractions import Fraction
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
BASE = HERE.parent
sys.path.insert(0, str(BASE))

from check_c5_dual import red_triangle_coordinates, verify


def search(args):
    import numpy as np
    from scipy.sparse import hstack
    from c5_anchor_columns import Model
    from c5_columns_warm import WarmLP

    model = Model(args.pool, "conditional", args.rho)
    excluded = red_triangle_coordinates()
    model.residual[sorted(excluded)] = 10000
    for path in args.seed:
        model.seed(path, cross_mode=True)
    solver = WarmLP(model, args.seconds, False)
    best = 0.0
    for step in range(args.rounds):
        print("step", step, "zero coordinates", len(excluded),
              "rank-one directions", len(model.dirs), flush=True)
        solution, dual = solver.solve(step, args.seconds)
        if solution is None:
            break
        matrix = hstack([model.static, *model.cols, model.target], format="csr")
        gamma = float(solution[-1])
        print("gamma", gamma, "minimum numerical residual",
              float(np.min(model.residual - matrix @ solution)), flush=True)
        if gamma > best + 1e-9:
            best = gamma
            model.save_exact_candidate(args.certificate, solution)
            result = verify(args.certificate, triangle_free=True, max_error=args.max_error)
            print(json.dumps(result), flush=True)
        additions = model.eigen_candidates(dual[:-1], dual[-1], per_block=4)[:60]
        if not additions:
            break
        solver.add_columns(additions)
        model.append(additions)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("--vendor", type=Path)
    parser.add_argument("--rho", type=Fraction, default=Fraction(3, 2))
    parser.add_argument("--max-error", type=Fraction, default=Fraction(1, 500))
    parser.add_argument("--pool", type=int, default=224)
    parser.add_argument("--rounds", type=int, default=5)
    parser.add_argument("--seconds", type=int, default=350)
    parser.add_argument("--seed", type=Path, action="append", default=[])
    parser.add_argument("--search", action="store_true")
    args = parser.parse_args()
    if not __debug__:
        raise RuntimeError("Run with Python assertions enabled")
    if args.vendor:
        sys.path.insert(0, str(args.vendor))
    if args.search:
        search(args)
    else:
        print(json.dumps(verify(args.certificate, triangle_free=True, max_error=args.max_error), indent=2))


if __name__ == "__main__":
    main()
