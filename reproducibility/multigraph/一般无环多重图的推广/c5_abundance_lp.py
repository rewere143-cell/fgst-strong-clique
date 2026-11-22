"""Numerical search for a dual inequality involving the induced marked C5 count."""
from pathlib import Path
from itertools import combinations, product
import argparse
import json
import time

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix, hstack, load_npz

from odd_cycle_parity_lp import ROOT, ORE, DATA, parity_target

HERE = Path(__file__).resolve().parent


def anchor_target(nvars):
    """Six-position coefficients counting the unused anchor-degree slots."""
    cycle = {(0, 1), (1, 2), (2, 3), (3, 4), (0, 4)}
    pairs6 = list(combinations(range(6), 2))
    idx6 = np.fromfile(ROOT / "flags/order6_orbit_index.bin", dtype="<i4")
    target = np.zeros(nvars, dtype=np.int64)
    for ext in product(range(3), repeat=5):
        positive = sum(c != 0 for c in ext)
        bad = 1 in ext or any(ext[i] and ext[j] for i, j in cycle)
        if not bad:
            continue
        code = sum((ext[i] if j == 5 else 2 * ((i, j) in cycle)) * 3**p
                   for p, (i, j) in enumerate(pairs6[1:]))
        orbit = int(idx6[code])
        if orbit >= 0:
            target[728 + orbit] += positive
    return target


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--pool", type=int, default=128)
    parser.add_argument("--seconds", type=int, default=180)
    parser.add_argument("--mode", choices=["abundance", "anchor"], default="abundance")
    args = parser.parse_args()

    start = time.monotonic()
    source = ROOT / "flags/sharp_face/compact/compact_R10000_simple_fourdefects_certificate.json"
    certificate = json.loads(source.read_text(encoding="utf-8"))
    n, nrows = certificate["variables"], certificate["equations"]
    cached = json.loads((ORE / "compact_exact_residual_cache.json").read_text(encoding="utf-8"))
    denominator = int(cached["denominator"])
    residual = np.array([int(x) / denominator for x in cached["residuals"]])
    keys = np.fromfile(DATA / "degree_keys.bin", dtype="<i8")
    values = np.fromfile(DATA / "degree_values.bin", dtype="<i4")
    degree = csr_matrix((values, (keys // n, keys % n)), shape=(nrows, n))
    degree_rows = (DATA / "degree.txt").read_text().splitlines()[1:]
    degree_rhs = np.array([row.startswith("2 ") for row in degree_rows], dtype=float)
    basis = load_npz(ROOT / "flags/sparse_refit/factor_coefficients.npz")
    metaload = np.load(ROOT / "flags/sparse_refit/factor_metadata.npz")
    norms, costs = metaload["norm"], metaload["cost"]
    factor_rows = certificate["rank_one_factors"]
    original = np.array([int(f["weight_numerator"]) / int(certificate["weight_denominator"])
                         for f in factor_rows]) * norms

    keep = set(np.argsort(-original)[:args.pool].tolist())
    for block in range(certificate["psd_blocks"]):
        choices = [i for i, f in enumerate(factor_rows) if f["block"] == block]
        if choices:
            keep.add(max(choices, key=lambda i: original[i]))
    keep = np.array(sorted(keep))
    all_effect = basis @ original
    basis = basis[:, keep]
    remainder = all_effect - basis @ original[keep]
    rem_cost = float(costs @ original - costs[keep] @ original[keep])

    q5, _ = parity_target(n)
    if args.mode == "abundance":
        target = np.zeros(n)
        target[q5] = -1
        raw_shift = 1/8
    else:
        target = anchor_target(n)
        raw_shift = 0.
    lhs = hstack([-degree.T, basis, csr_matrix(remainder[:, None]),
                  csr_matrix(target[:, None])], format="csr")
    constants = np.r_[degree_rhs, costs[keep], rem_cost, raw_shift]
    objective = np.zeros(lhs.shape[1])
    objective[-1] = -1
    print(f"LP {lhs.shape}, {lhs.nnz} nnz, cycle coordinate {q5}", flush=True)
    sol = linprog(
        objective, A_ub=lhs, b_ub=residual,
        A_eq=csr_matrix(constants[None, :]), b_eq=[0.],
        bounds=[(None, None)] * nrows + [(-float(original[i]), None) for i in keep]
        + [(-1., None), (0., 10.)],
        method="highs-ipm",
        options={"time_limit": args.seconds, "disp": True,
                 "ipm_optimality_tolerance": 1e-9,
                 "primal_feasibility_tolerance": 1e-8,
                 "dual_feasibility_tolerance": 1e-8},
    )
    out = {"numerical_only": True, "pool": args.pool, "mode": args.mode, "status": sol.message,
           "success": sol.success, "active_factors": int(len(keep)),
           "seconds": time.monotonic() - start}
    if sol.x is not None:
        out.update(gamma=float(sol.x[-1]),
                   min_residual=float(np.min(residual-lhs @ sol.x)),
                   constant_equality_error=float(constants @ sol.x))
        np.savez_compressed(HERE/f"c5_{args.mode}_numerical_{args.pool}.npz",
                            result=sol.x, keep=keep, norms=norms,
                            lambda_delta=sol.x[:nrows], weight_original=original)
    (HERE/f"c5_{args.mode}_numerical_{args.pool}.json").write_text(
        json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(out, indent=2), flush=True)


if __name__ == "__main__":
    main()
