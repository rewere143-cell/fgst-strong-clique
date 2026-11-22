"""Numerical column generation for the induced C5 anchor-slot penalty.

The dual of a restricted scalar LP prices arbitrary rank-one PSD columns.
Integer rounded vectors lie in the exact C5 equality kernel. Only the
separate check_c5_dual.py replay supplies a proof.
"""
import argparse
import json
from pathlib import Path
import sys
import time

import numpy as np
from scipy.optimize import linprog
from scipy.linalg import eigh, null_space
from scipy.sparse import csr_matrix, hstack, load_npz

from c5_abundance_lp import ROOT, ORE, DATA, HERE, anchor_target, parity_target
from check_c5_dual import BASE, CONDITIONAL_RHO, degree_row_names, load_json

FACE = ROOT / "flags/sharp_face"
sys.path.insert(0, str(FACE))
from c5_face_helpers import constraint_numerator, round_kernel_factor


class Model:
    def __init__(self, pool, mode="anchor", conditional_rho=CONDITIONAL_RHO):
        self.mode = mode
        self.conditional_rho = conditional_rho
        self.certificate = load_json(BASE)
        n, nrows = self.certificate["variables"], self.certificate["equations"]
        self.n, self.nrows = n, nrows
        self.r = int(self.certificate["vector_denominator"])
        cache = load_json(ORE / "compact_exact_residual_cache.json")
        denom = int(cache["denominator"])
        self.residual = np.array([int(x)/denom for x in cache["residuals"]])
        keys = np.fromfile(DATA / "degree_keys.bin", dtype="<i8")
        values = np.fromfile(DATA / "degree_values.bin", dtype="<i4")
        self.degree = csr_matrix((values, (keys % n, keys // n)), shape=(n, nrows))
        degree_rows, _ = degree_row_names(DATA)
        self.degree_rhs = np.array([k == 2 for k, _, _ in degree_rows], dtype=float)

        self.face = load_json(FACE / "c5_face_data.json")["blocks"]
        lines = iter((DATA / "basis.txt").read_text().splitlines())
        variables, blocks = map(int, next(lines).split())
        assert variables == n and blocks == len(self.face)
        self.offsets = [0]
        self.units = []
        self.kernels = []
        for data in self.face:
            k, _, m = map(int, next(lines).split())
            basis = [tuple(map(int, next(lines).split())) for _ in range(m)]
            self.offsets.append(self.offsets[-1]+m*m)
            unit_indices = [j for j, (h, _) in enumerate(basis) if h == 2]
            assert len(unit_indices) in (0, 1) and (k == 2) == bool(unit_indices)
            self.units.append(unit_indices[0] if unit_indices else None)
            assert m == data["size"]
            self.kernels.append(null_space(constraint_numerator(data).astype(float))
                                if data["rank"] else None)
        gkeys = np.fromfile(DATA / "keys.bin", dtype="<i8")
        gvalues = np.fromfile(DATA / "values.bin", dtype="<i4")
        self.gram = csr_matrix((gvalues, (gkeys // n, gkeys % n)),
                               shape=(self.offsets[-1], n), dtype=float)
        self.parts = [self.gram[i:j].tocsc() for i, j in zip(self.offsets, self.offsets[1:])]

        basis = load_npz(ROOT / "flags/sparse_refit/factor_coefficients.npz")
        meta = np.load(ROOT / "flags/sparse_refit/factor_metadata.npz")
        self.norms, costs = meta["norm"], meta["cost"]
        factors = self.certificate["rank_one_factors"]
        q = self.certificate["weight_denominator"]
        self.original = self.norms * np.array([int(f["weight_numerator"])/int(q) for f in factors])
        keep = set(np.argsort(-self.original)[:pool].tolist())
        for block in range(blocks):
            choices = [i for i, f in enumerate(factors) if f["block"] == block]
            if choices:
                keep.add(max(choices, key=lambda i: self.original[i]))
        self.initial = np.array(sorted(keep))
        chosen = basis[:, self.initial]
        remaining = basis @ self.original - chosen @ self.original[self.initial]
        remaining_cost = float(costs @ self.original - costs[self.initial] @ self.original[self.initial])
        self.static = hstack([-self.degree, chosen, csr_matrix(remaining[:, None])], format="csc")
        self.static_costs = np.r_[self.degree_rhs, costs[self.initial], remaining_cost]
        self.static_bounds = ([(None, None)] * nrows
                              + [(-float(self.original[i]), None) for i in self.initial]
                              + [(-1., None)])
        if mode == "anchor":
            self.target = csr_matrix(anchor_target(n).astype(float)[:, None])
            self.target_cost = 0.
        elif mode == "abundance":
            q_cycle, _ = parity_target(n)
            self.target = csr_matrix(([-1.], ([q_cycle], [0])), shape=(n, 1))
            self.target_cost = 1/8
        elif mode == "conditional":
            q_cycle, _ = parity_target(n)
            coefficients = anchor_target(n).astype(float)
            coefficients[q_cycle] -= float(conditional_rho)
            self.target = csr_matrix(coefficients[:, None])
            self.target_cost = float(conditional_rho)/8
        else:
            _, coefficients = parity_target(n)
            self.target = csr_matrix(coefficients.astype(float)[:, None])
            self.target_cost = 0.
        self.dirs = []
        self.cols = []
        self.costs = []
        self.seen = set()

    def eigen_candidates(self, y, y_eq, per_block):
        prices = self.gram @ y
        ret = []
        for block, (i, j) in enumerate(zip(self.offsets, self.offsets[1:])):
            m = self.face[block]["size"]
            mat = prices[i:j].copy().reshape(m, m)
            unit = self.units[block]
            if unit is not None:
                mat[unit, unit] += y_eq
            mat = (mat + mat.T) / 2
            kernel = self.kernels[block]
            if kernel is not None:
                mat = kernel.T @ mat @ kernel
            size = mat.shape[0]
            if size == 0:
                continue
            vals, vectors = eigh(mat, subset_by_index=[max(0, size-per_block), size-1])
            for val, vector in zip(vals, vectors.T):
                if val <= 1e-8:
                    continue
                if kernel is not None:
                    vector = kernel @ vector
                integer = round_kernel_factor(vector, self.face[block], self.r, project=False)
                scale = -1 if next((x for x in integer if x), 0) < 0 else 1
                integer = tuple(scale*x for x in integer)
                key = (block, integer)
                if key in self.seen:
                    continue
                v = np.array(integer)/self.r
                coef = np.asarray(self.parts[block].T @ np.outer(v, v).ravel()).ravel()
                cost = float(v[unit]**2) if unit is not None else 0.
                score = y @ coef + y_eq * cost
                if score > 1e-8:
                    ret.append((float(score), key, csr_matrix(coef[:, None]), cost))
        return sorted(ret, key=lambda row: -row[0])

    def solve(self, seconds, method):
        lhs = hstack([self.static, *self.cols, self.target], format="csc")
        constants = np.r_[self.static_costs, self.costs, self.target_cost]
        objective = np.zeros(lhs.shape[1])
        objective[-1] = -1.
        options = {
            "time_limit": seconds, "disp": False,
            "ipm_optimality_tolerance": 1e-8,
            "primal_feasibility_tolerance": 1e-8,
            "dual_feasibility_tolerance": 1e-8,
        }
        sol = linprog(objective, A_ub=lhs, b_ub=self.residual,
                      A_eq=constants[None, :], b_eq=[0.],
                      bounds=self.static_bounds+[(0., None)]*len(self.dirs)+[(0., 10.)],
                      method=method, options=options)
        return sol, lhs, constants

    def save_exact_candidate(self, path, result):
        wide_weight = 10**14
        wide_t = wide_weight*self.r**2
        base_q = int(self.certificate["weight_denominator"])
        base_t = int(self.certificate["common_denominator"])
        nrows = self.nrows
        selected = dict(zip(map(int, self.initial), result[nrows:nrows+len(self.initial)]))
        remaining = 1 + float(result[nrows+len(self.initial)])
        weights = []
        for i, f in enumerate(self.certificate["rank_one_factors"]):
            original = int(f["weight_numerator"])/base_q
            if i in selected:
                updated = original + float(selected[i])/float(self.norms[i])
            else:
                updated = original*remaining
            weights.append(max(0, round(updated*wide_weight)))
        extra = []
        for (block, integers), weight in zip(self.dirs, result[nrows+len(self.initial)+1:-1]):
            wn = round(float(weight)*wide_weight)
            if wn > 0:
                extra.append({"block": block, "vector_numerators": integers, "weight_numerator": wn})
        _, names = degree_row_names(DATA)
        degree_weights = []
        for name, delta in zip(names, result[:nrows]):
            original = int(self.certificate["degree_weights_numerators"].get(name, 0))/base_t
            degree_weights.append(str(round((original+float(delta))*wide_t)))
        import hashlib
        scale = self.conditional_rho.denominator if self.mode == "conditional" else 1
        gamma = scale * round(float(result[-1])*wide_t/scale)
        data = {
            "mode": self.mode,
            "source_rank_one_vectors_sha256": hashlib.sha256(BASE.read_bytes()).hexdigest(),
            "weight_denominator": wide_weight, "factor_weights": weights,
            "extra_rank_one_factors": extra,
            "degree_weights_numerators": degree_weights,
            "gamma_numerator_at_common_denominator": str(gamma),
        }
        if self.mode == "conditional":
            data["anchor_ratio"] = str(self.conditional_rho)
        path.write_text(json.dumps(data, separators=(",", ":"))+"\n", encoding="utf-8")
        return len(extra)

    def append(self, additions):
        for _, key, column, cost in additions:
            self.seen.add(key)
            self.dirs.append(key)
            self.cols.append(column)
            self.costs.append(cost)

    def seed(self, path, *, cross_mode=False):
        old = load_json(path)
        if old["mode"] != self.mode and not cross_mode:
            raise ValueError("Seed kind differs from requested model")
        for factor in old.get("extra_rank_one_factors", []):
            block = int(factor["block"])
            integers = tuple(factor["vector_numerators"])
            if (block, integers) in self.seen:
                continue
            v = np.asarray(integers)/self.r
            coefficient = np.asarray(self.parts[block].T @ np.outer(v, v).ravel()).ravel()
            unit = self.units[block]
            cost = float(v[unit]**2) if unit is not None else 0.
            self.append([(0., (block, integers), csr_matrix(coefficient[:, None]), cost)])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pool", type=int, default=128)
    parser.add_argument("--mode", choices=["anchor", "abundance", "parity", "conditional"], default="anchor")
    parser.add_argument("--rounds", type=int, default=12)
    parser.add_argument("--seconds", type=int, default=200, help="Per-round optimization limit")
    parser.add_argument("--columns", type=int, default=48)
    parser.add_argument("--per-block", type=int, default=3)
    parser.add_argument("--method", default="highs-ipm", choices=["highs-ipm", "highs-ds"])
    parser.add_argument("--seed", type=Path)
    parser.add_argument("--result", type=Path)
    args = parser.parse_args()
    model = Model(args.pool, args.mode)
    if args.seed:
        model.seed(args.seed)
    path = args.result or HERE/f"c5_{args.mode}_column_candidate.json"
    best = 0.
    for round_index in range(args.rounds):
        start = time.monotonic()
        print("start", round_index, "extra columns", len(model.cols), flush=True)
        sol, lhs, constants = model.solve(args.seconds, args.method)
        if not sol.success:
            print(sol.message, flush=True)
            break
        gamma = float(sol.x[-1])
        print("round", round_index, "gamma", gamma, "min residual",
              float(np.min(model.residual-lhs @ sol.x)), "raw error",
              float(sol.x @ constants), "solve seconds", time.monotonic()-start, flush=True)
        if gamma > best + 1e-9:
            best = gamma
            extra_count = model.save_exact_candidate(path, sol.x)
            print("candidate saved; nonzero extra weights", extra_count, flush=True)
        additions = model.eigen_candidates(sol.ineqlin.marginals, sol.eqlin.marginals[0],
                                           args.per_block)
        print("priced directions", len(additions), "positive scores",
              [item[0] for item in additions[:5]], flush=True)
        if not additions:
            break
        model.append(additions[:args.columns])


if __name__ == "__main__":
    main()

