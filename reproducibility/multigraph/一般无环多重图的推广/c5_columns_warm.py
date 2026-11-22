"""Column search with a warm HiGHS basis and exact-candidate snapshots."""
import argparse
from pathlib import Path
import time

import highspy as highs
import numpy as np
from scipy.sparse import csr_matrix, hstack, vstack

from c5_anchor_columns import Model, HERE
from check_c5_dual import load_json


def check(status):
    if status == highs.HighsStatus.kError:
        raise RuntimeError(f"HiGHS status {status}")


class WarmLP:
    def __init__(self, model, initial_seconds, verbose):
        self.h = highs.Highs()
        self.model = model
        gramcols = model.cols
        self.gamma_col = model.static.shape[1]
        bounds = model.static_bounds + [(0., 10.)]+[(0., None)]*len(gramcols)
        lhs = hstack([model.static, model.target, *gramcols], format="csc")
        eq = np.r_[model.static_costs, model.target_cost, model.costs]
        matrix = vstack([lhs, csr_matrix(eq[None, :])], format="csc")
        matrix.eliminate_zeros()
        self.objective = np.zeros(matrix.shape[1])
        self.objective[self.gamma_col] = -1.
        lp = highs.HighsLp()
        lp.num_col_, lp.num_row_ = matrix.shape[1], matrix.shape[0]
        lp.col_cost_ = self.objective
        lp.col_lower_ = [-highs.kHighsInf if a is None else a for a, _ in bounds]
        lp.col_upper_ = [highs.kHighsInf if b is None else b for _, b in bounds]
        lp.row_lower_ = np.r_[np.full(lhs.shape[0], -highs.kHighsInf), 0.]
        lp.row_upper_ = np.r_[model.residual, 0.]
        lp.a_matrix_.num_col_, lp.a_matrix_.num_row_ = lp.num_col_, lp.num_row_
        lp.a_matrix_.format_ = highs.MatrixFormat.kColwise
        lp.a_matrix_.start_ = matrix.indptr.astype(np.int32, copy=False)
        lp.a_matrix_.index_ = matrix.indices.astype(np.int32, copy=False)
        lp.a_matrix_.value_ = matrix.data
        for name, value in (
            ("threads", 1), ("output_flag", verbose),
            ("dual_feasibility_tolerance", 1e-8), ("primal_feasibility_tolerance", 1e-8),
            ("ipm_optimality_tolerance", 1e-9), ("run_crossover", "on"),
            ("time_limit", initial_seconds), ("solver", "ipm"),
        ):
            check(self.h.setOptionValue(name, value))
        check(self.h.passModel(lp))

    def add_columns(self, additions):
        matrix = vstack([
            hstack([row[2] for row in additions], format="csc"),
            csr_matrix([[row[3] for row in additions]]),
        ], format="csc")
        matrix.eliminate_zeros()
        count = matrix.shape[1]
        old_basis = self.h.getBasis()
        check(self.h.addCols(count, np.zeros(count), np.zeros(count),
                             np.full(count, highs.kHighsInf), matrix.nnz,
                             matrix.indptr[:-1].astype(np.int32, copy=False),
                             matrix.indices.astype(np.int32, copy=False), matrix.data))
        if old_basis.valid and not self.h.getBasis().valid:
            basis = highs.HighsBasis()
            basis.col_status = list(old_basis.col_status)+[highs.HighsBasisStatus.kLower]*count
            basis.row_status = old_basis.row_status
            check(self.h.setBasis(basis))

    def solve(self, iteration, seconds):
        if iteration:
            check(self.h.setOptionValue("solver", "simplex"))
            check(self.h.setOptionValue("simplex_strategy", 4))
            check(self.h.setOptionValue("presolve", "off"))
            check(self.h.setOptionValue("time_limit", seconds))
        check(self.h.run())
        status = self.h.getModelStatus()
        if status != highs.HighsModelStatus.kOptimal:
            print("Stopped", status, self.h.getInfo().max_primal_infeasibility, flush=True)
            return None, None
        result = self.h.getSolution()
        assert result.value_valid and result.dual_valid
        x = np.asarray(result.col_value)
        # Preserve the candidate writer's convention: the gamma variable is last.
        candidate = np.r_[x[:self.gamma_col], x[self.gamma_col+1:], x[self.gamma_col]]
        return candidate, np.asarray(result.row_dual)


def seed(model, path):
    old = load_json(path)
    if old["mode"] != model.mode:
        raise ValueError("Seed kind differs from requested model")
    for factor in old.get("extra_rank_one_factors", []):
        block = int(factor["block"])
        integers = tuple(factor["vector_numerators"])
        v = np.asarray(integers)/model.r
        coefficient = np.asarray(model.parts[block].T @ np.outer(v, v).ravel()).ravel()
        unit = model.units[block]
        cost = float(v[unit]**2) if unit is not None else 0.
        model.append([(0., (block, integers), csr_matrix(coefficient[:, None]), cost)])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mode", choices=["anchor", "abundance", "parity"], default="anchor")
    parser.add_argument("--pool", type=int, default=128)
    parser.add_argument("--rounds", type=int, default=25)
    parser.add_argument("--initial-seconds", type=float, default=500.)
    parser.add_argument("--seconds", type=float, default=180.)
    parser.add_argument("--columns", type=int, default=48)
    parser.add_argument("--per-block", type=int, default=3)
    parser.add_argument("--seed", type=Path)
    parser.add_argument("--result", type=Path)
    parser.add_argument("--verbose", action="store_true")
    args = parser.parse_args()
    model = Model(args.pool, args.mode)
    if args.seed:
        seed(model, args.seed)
    result_path = args.result or HERE/f"c5_{args.mode}_warm_candidate.json"
    warm = WarmLP(model, args.initial_seconds, args.verbose)
    best = 0.
    for round_index in range(args.rounds):
        start = time.monotonic()
        print("start", round_index, "directions", len(model.dirs), flush=True)
        x, y = warm.solve(round_index, args.seconds)
        if x is None:
            break
        gamma = float(x[-1])
        info = warm.h.getInfo()
        print("round", round_index, "gamma", gamma,
              "max infeasibility", info.max_primal_infeasibility, "iterations",
              (info.ipm_iteration_count, info.simplex_iteration_count),
              "seconds", time.monotonic()-start, flush=True)
        if gamma > best+1e-9:
            best = gamma
            count = model.save_exact_candidate(result_path, x)
            print("candidate saved with", count, "extra weights", flush=True)
        additions = model.eigen_candidates(y[:-1], y[-1], args.per_block)
        print("priced", len(additions), "best scores", [row[0] for row in additions[:5]], flush=True)
        if not additions:
            break
        additions = additions[:args.columns]
        warm.add_columns(additions)
        model.append(additions)


if __name__ == "__main__":
    main()

