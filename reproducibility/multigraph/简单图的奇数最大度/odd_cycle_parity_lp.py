"""Numerical exploration of the anchored odd-degree parity row.

This uses audited orbit indexes to build a new target. LP output is not an
exact dual certificate. Default: try strengthening the sharp objective by
gamma times the odd-neighbor extension sum; --degree uses the parity row to
bound the objective at one fixed odd degree.
"""
import argparse
from itertools import combinations, product
import json
from pathlib import Path
import time

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix, hstack, load_npz

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent / "regeneration_20261105/source_full/extracted/strong_clique"
DATA = ROOT / "audit/flag_coefficients"
ORE = ROOT / "ore"


def pairs(n):
    return tuple(combinations(range(n), 2))


def decode(n, code):
    colors = [2]
    for _ in pairs(n)[1:]:
        colors.append(code % 3)
        code //= 3
    assert code == 0
    return colors


def indexes():
    return {n: np.fromfile(DATA / f"idx{n}.bin", dtype="<i4") for n in range(3, 6)} | {
        6: np.fromfile(ROOT / "flags/order6_orbit_index.bin", dtype="<i4")
    }


def parity_target(nvars):
    cycle = { (0, 1), (1, 2), (2, 3), (3, 4), (0, 4) }
    pairs5 = list(combinations(range(5), 2))
    pairs6 = list(combinations(range(6), 2))
    idx5 = np.fromfile(DATA / "idx5.bin", dtype="<i4")
    idx6 = np.fromfile(ROOT / "flags/order6_orbit_index.bin", dtype="<i4")
    code5 = sum(2 * 3**j for j, pair in enumerate(pairs5[1:]) if pair in cycle)
    q5 = int(idx5[code5])
    assert 0 <= q5 < 728 and len(idx6) == 3**14
    target = np.zeros(nvars, dtype=np.int64)
    for ext in product(range(3), repeat=5):
        if sum(c != 0 for c in ext) % 2 == 0:
            continue
        code = sum((ext[i] if j == 5 else 2 * ((i, j) in cycle)) * 3**p
                   for p, (i, j) in enumerate(pairs6[1:]))
        orbit = int(idx6[code])
        if orbit >= 0:
            target[728 + orbit] += 1
    return q5, target


def injective_rows(nvars, degree):
    """Rows c+f*q >=0 from injective color-preserving map counts."""
    ids = indexes()
    stirling = [[1]]
    for n in range(1, 7):
        prev = stirling[-1] + [0]
        stirling.append([0] + [prev[j-1] - (n-1)*prev[j] for j in range(1,n+1)])
    powers = {n: tuple(3**i for i in range(len(pairs(n))-1)) for n in range(2,7)}
    keys, values, constants = [], [], []
    for n in range(3, 7):
        valid = np.flatnonzero(ids[n] >= 0)
        representative = np.full(int(ids[n].max())+1, len(ids[n]), dtype=np.int32)
        np.minimum.at(representative, ids[n][valid], valid)
        for orbit, code in enumerate(representative):
            if code >= len(ids[n]):
                continue
            colors = decode(n, int(code))
            colored = [[0] * n for _ in range(n)]
            for (i, j), c in zip(pairs(n), colors):
                colored[i][j] = colored[j][i] = c
            classes = {}
            for i, row in enumerate(colored):
                classes.setdefault(tuple(row), []).append(i)
            twins = list(classes.values())
            if len(twins) == n:
                continue
            col = len(constants)
            const = 0.0
            for shape in product(*(range(1, len(klass)+1) for klass in twins)):
                if sum(shape) == n:
                    q, coef = orbit + (728 if n == 6 else 0), 1.
                else:
                    keep = sorted(i for klass, s in zip(twins, shape) for i in klass[:s])
                    size = len(keep)
                    coef = 1. / degree**(n-size)
                    for klass, s in zip(twins, shape):
                        coef *= stirling[len(klass)][s]
                    assert keep[:2] == [0,1]
                    if size == 2:
                        const += coef
                        continue
                    quot = sum(p * colored[keep[i]][keep[j]]
                               for p, (i,j) in zip(powers[size], pairs(size)[1:]))
                    q = int(ids[size][quot]) + (728 if size == 6 else 0)
                    assert ids[size][quot] >= 0
                keys.append((q,col))
                values.append(coef)
            constants.append(const)
    i,j = zip(*keys)
    return csr_matrix((values,(i,j)), shape=(nvars,len(constants))), np.array(constants)


def conditional_half_rows(nvars, degree, include_all=False):
    """Integer constraints for one-vertex extensions with half-count on C5."""
    colors = [[2 * ((i-j) % 5 in (1,4)) for j in range(5)] for i in range(5)]
    lines = iter((DATA / "basis.txt").read_text().splitlines())
    _, nblocks = map(int,next(lines).split())
    offset = 0
    triples = []
    for _ in range(nblocks):
        k, code, m = map(int,next(lines).split())
        flags = [tuple(map(int,next(lines).split())) for i in range(m)]
        assert flags[0] == (k,code)
        type_colors = decode(k,code)
        roots = [f for f in product(range(5),repeat=k)
                 if all(colors[f[i]][f[j]] == c for (i,j),c in zip(pairs(k),type_colors))]
        for j, (n, fr) in enumerate(flags):
            if n != k+1 or (not include_all and not roots):
                continue
            extension_pipes = [(i,c) for (i,h),c in zip(pairs(n),decode(n,fr)) if h == k]
            if include_all or all(sum(all(colors[f[i]][x] == c for i,c in extension_pipes)
                       for x in range(5)) == 1 for f in roots):
                triples.append((offset+j*m+j, offset+j, offset, k == 2))
        offset += m*m
    assert 0 < len(triples)
    dkeys = np.fromfile(DATA / "keys.bin", dtype="<i8")
    vals = np.fromfile(DATA / "values.bin", dtype="<i4")
    gram = csr_matrix((vals,(dkeys//nvars,dkeys%nvars)),shape=(offset,nvars))
    const_coef = (degree**2-1)/(4*degree**2)
    columns, constants = [], []
    for square, first, unit, is_const in triples:
        row = gram[square] - gram[first]
        if not is_const:
            row = row + const_coef * gram[unit]
        columns.append(row.T)
        constants.append(const_coef if is_const else 0.0)
    return hstack(columns, format="csr"), np.array(constants)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--pool", type=int, default=128)
    parser.add_argument("--degree", type=int)
    parser.add_argument("--finite", action="store_true")
    parser.add_argument("--lattice-all", action="store_true")
    parser.add_argument("--seconds", type=int, default=180)
    options = parser.parse_args()
    assert options.degree is None or (options.degree > 0 and options.degree % 2)
    assert not options.finite or options.degree
    assert not options.lattice_all or options.finite
    start = time.monotonic()
    source = ROOT / "flags/sharp_face/compact/compact_R10000_simple_fourdefects_certificate.json"
    certificate = json.loads(source.read_text(encoding="utf-8"))
    n, nrows = certificate["variables"], certificate["equations"]
    cached = json.loads((ORE / "compact_exact_residual_cache.json").read_text(encoding="utf-8"))
    denominator = int(cached["denominator"])
    residual = np.array([int(x) / denominator for x in cached["residuals"]])
    keys = np.fromfile(DATA / "degree_keys.bin", dtype="<i8")
    values = np.fromfile(DATA / "degree_values.bin", dtype="<i4")
    a = csr_matrix((values, (keys // n, keys % n)), shape=(nrows, n))
    degree_rows = (DATA / "degree.txt").read_text().splitlines()[1:]
    degree_rhs = np.array([row.startswith("2 ") for row in degree_rows], dtype=float)
    assert len(degree_rhs) == nrows and sum(degree_rhs) == 1
    basis = load_npz(ROOT / "flags/sparse_refit/factor_coefficients.npz")
    meta = np.load(ROOT / "flags/sparse_refit/factor_metadata.npz")
    factors = certificate["rank_one_factors"]
    base = np.array([int(f["weight_numerator"]) / int(certificate["weight_denominator"])
                     for f in factors]) * meta["norm"]
    keep = set(np.argsort(-base)[:options.pool].tolist())
    for block in range(certificate["psd_blocks"]):
        choices = [i for i, f in enumerate(factors) if f["block"] == block]
        if choices:
            keep.add(max(choices, key=lambda i: base[i]))
    keep = np.array(sorted(keep))
    all_effect = basis @ base
    basis = basis[:, keep]
    remainder = all_effect - basis @ base[keep]
    costs = meta["cost"]
    rem_cost = float(costs @ base - costs[keep] @ base[keep])
    q5, target = parity_target(n)
    direct = float(min(residual[target > 0] / target[target > 0]))
    target_for_lp = target.astype(float)
    if options.degree:
        target_for_lp[q5] -= 1 / options.degree
    parts = [-a.T, basis, csr_matrix(remainder[:, None])]
    constants = [degree_rhs, costs[keep], [rem_cost]]
    if options.finite:
        inj, con1 = injective_rows(n, options.degree)
        half, con2 = conditional_half_rows(n, options.degree, options.lattice_all)
        print("Finite constraints:", inj.shape[1], "injectivity and",
              half.shape[1], "integer conditional counts.", flush=True)
        parts.extend([inj,half])
        constants.extend([con1,con2])
    parts.append(csr_matrix(target_for_lp[:,None]))
    constants.append([0.])
    lhs = hstack(parts,format="csr")
    bound_change = np.concatenate(constants)
    if options.degree:
        objective = bound_change
        equality, eq_rhs = None, None
    else:
        objective = np.zeros(lhs.shape[1])
        objective[-1] = -1
        equality, eq_rhs = csr_matrix(bound_change[None, :]), [0.]
    print(f"LP {lhs.shape}, {lhs.nnz} nnz, cycle coordinate {q5}, "
          f"{int(target.sum())} extensions in {int((target != 0).sum())} orbits", flush=True)
    result = linprog(
        objective, A_ub=lhs, b_ub=residual, A_eq=equality, b_eq=eq_rhs,
        bounds=[(None, None)] * nrows + [(-float(base[i]), None) for i in keep]
        + [(-1., None)] + [(0.,None)] * (lhs.shape[1]-nrows-len(keep)-2)
        + [(0., 5.) if not options.degree else (0., None)],
        method="highs-ipm",
        options={"time_limit": options.seconds, "disp": True,
                 "ipm_optimality_tolerance": 1e-9,
                 "primal_feasibility_tolerance": 1e-8,
                 "dual_feasibility_tolerance": 1e-8},
    )
    out = {
        "numerical_only": True, "status": result.message,
        "success": result.success, "seconds": time.monotonic() - start,
        "degree": options.degree, "cycle_coordinate": q5,
        "extension_multiplicities": {str(i): int(target[i]) for i in np.flatnonzero(target)},
        "direct_unmodified_gamma": direct,
        "active_factors": int(len(keep)),
        "finite_constraints": options.finite,
        "lattice_all": options.lattice_all,
    }
    if result.x is not None:
        out.update(gamma=float(result.x[-1]),
                   bound=float(1.25 + bound_change @ result.x),
                   min_residual=float(np.min(residual - lhs @ result.x)))
        if options.degree:
            out["odd_target"] = (5 * options.degree**2 - 2 * options.degree + 1) / (4 * options.degree**2)
    suffix = "_finite_all" if options.lattice_all else "_finite" if options.finite else ""
    name = f"odd_cycle_parity_lp_{options.degree or 'gamma'}_pool{options.pool}{suffix}.json"
    (HERE / name).write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(out, indent=2), flush=True)


if __name__ == "__main__":
    main()
