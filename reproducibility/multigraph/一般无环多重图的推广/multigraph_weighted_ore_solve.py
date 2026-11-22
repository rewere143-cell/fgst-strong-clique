"""Numerically solve the weighted marked-bipartite Ore relaxation."""

import argparse
from fractions import Fraction
import json
from math import comb, factorial
from pathlib import Path
import sys

from multigraph_lift_probe import decode, edge_pairs


def objective_channels(data):
    import numpy as np

    tags = np.asarray([int(mask).bit_count() for mask in data["mask"]], dtype=np.int8)
    objective = np.asarray(data["twice_obj"], dtype=np.float64)/2
    return tags, [(tags == k)*objective for k in range(3)], objective


def local_defect(data):
    import numpy as np

    from multigraph_weighted_ore_model import permutation_slots

    result = np.zeros(len(data["order"]))
    perms = np.asarray(permutation_slots(3), dtype=np.intp)
    for row in np.flatnonzero(data["order"] == 3):
        colors = np.asarray(decode(3, int(data["code"][row])))
        mask = data["mask"][row]
        root = colors[perms[:, 0]] == 2
        if not mask:
            if np.all(colors == 2):
                result[row] = len(perms)
            else:
                result[row] = np.count_nonzero(root & (colors[perms[:, 1]] == 1))
        elif int(mask).bit_count() == 1:
            result[row] = np.count_nonzero(
                root & (colors[perms[:, 1]] == 2) & ((1 << perms[:, 1]) == mask)
            )
    return result


def extra_rows(data, lower, upper, simple_bound, shadow_bound, use_caps, max_degree):
    import numpy as np
    from scipy.sparse import csr_matrix, coo_matrix, vstack

    order = data["order"]
    tags, (o0, o1, o2), objective = objective_channels(data)
    q0 = np.where((order == 2) & (tags == 0), 2, 0)
    q1 = np.where((order == 2) & (tags == 1), 2, 0)
    norm = data["normalizer"]
    eta = float(shadow_bound)
    rows = [
        o2+o1/2-eta*norm, o2-eta*q1, o1/2-eta*q0,
    ]
    if simple_bound:
        beta = float(simple_bound)
        rows.extend((o0+o1/2-beta*norm, o0-beta*q0, o1/2-beta*q1))
    if max_degree:
        rows.append(o0+0.45*local_defect(data)-1.25*q0)
    if lower or upper != 1:
        lo, hi = float(lower), float(upper)
        rows.extend((lo*norm-q1, q1-hi*norm))
        zero = ((1-hi)**2, (1-lo)**2)
        one = (min(2*lo*(1-lo), 2*hi*(1-hi)),
               0.5 if lo <= 0.5 <= hi else max(2*lo*(1-lo), 2*hi*(1-hi)))
        two = (lo**2, hi**2)
        for bounds, channel in zip((zero, one, two), (o0, o1, o2)):
            rows.extend((bounds[0]*objective-channel, channel-bounds[1]*objective))
    matrix = csr_matrix(np.asarray(rows))
    if use_caps:
        index = []
        columns = []
        values = []
        count = 0
        for n in range(3, int(max(order))+1):
            for k in range(0, n):
                hits = np.flatnonzero((order == n) & (tags == k))
                if not len(hits):
                    continue
                root = np.flatnonzero(q1 if k else q0)[0]
                choose = comb(n-2, k-1) if k else 1
                factor = Fraction(n**(n-3)*choose, max(1, k)*factorial(n-2))
                index.extend([count]*(len(hits)+1))
                columns.extend(hits)
                columns.append(root)
                values.extend([1]*len(hits))
                values.append(-2*float(factor))
                count += 1
        caps = coo_matrix((values, (index, columns)), shape=(count, len(order))).tocsr()
        matrix = vstack((matrix, caps), format="csr")
    return matrix


def red_biclique_seed(data):
    import numpy as np

    result = np.zeros(len(data["order"]))
    for row, (n, c, mask, aut) in enumerate(zip(
        data["order"], data["code"], data["mask"], data["aut_count"],
    )):
        if mask:
            continue
        colors = decode(n, c)
        side = [0]*n
        for color, (u, v) in zip(colors, edge_pairs(n)):
            if u == 0:
                side[v] = int(color == 2)
        if all(color == 2*(side[u] != side[v]) for color, (u, v) in zip(colors, edge_pairs(n))):
            result[row] = 2.0**(-(n-2))/aut
    return result


def pentagon_seed(data):
    import numpy as np

    from audit_multigraph_type_forest_psd import direct_maps

    colors = [[2*int((i-j) % 5 in (1, 4)) for j in range(5)] for i in range(5)]
    order = int(max(data["order"]))
    maps = {n: direct_maps(colors, n) for n in range(2, order+1)}
    return np.asarray([
        0 if mask else len(maps[n].get(code, ()))/(10*2.0**(n-2)*aut)
        for n, code, mask, aut in zip(data["order"], data["code"], data["mask"], data["aut_count"])
    ])


def solve(cache, output, method, seconds, iterations, lower, upper, simple_bound, use_caps,
          with_ratio_psd, sample_bounds, mixed, local_beta, blend=False):
    import numpy as np
    from scipy.optimize import linprog
    from scipy.sparse import coo_matrix, csr_matrix, eye, hstack, load_npz, vstack

    data = dict(np.load(cache.with_suffix(".data.npz")))
    degree = load_npz(cache.with_suffix(".ore.npz"))
    max_degree = bool(data.get("max_degree", False))
    if simple_bound is None:
        simple_bound = Fraction(5, 4) if max_degree else Fraction(273323, 10**6)
    shadow_bound = Fraction(1, 2) if max_degree else Fraction(1, 4)
    if max_degree and sample_bounds and 1 <= sample_bounds[0] <= 2:
        low_mass = sample_bounds[0]
        shadow_bound = low_mass-low_mass*low_mass/2
    target = Fraction(5, 4) if max_degree else Fraction(1, 4)
    _, channels, objective = objective_channels(data)
    extras = extra_rows(data, lower, upper, simple_bound, shadow_bound, use_caps, max_degree)
    normalizer = data["normalizer"]
    equality = vstack((csr_matrix(normalizer), degree), format="csr") if max_degree else csr_matrix(normalizer)
    eq_rhs = np.r_[1, np.zeros(equality.shape[0]-1)]
    d = extras if max_degree else vstack((degree, extras), format="csr")
    if sample_bounds:
        sample_meta = dict(np.load(cache.with_suffix(".sample_meta.npz")))
        sample = load_npz(cache.with_suffix(".sample.npz"))
        sample_tagged = load_npz(cache.with_suffix(".sample_tagged.npz"))
        column = sample_meta["extension_parents"]
        left = coo_matrix(
            (data["aut_count"][column], (np.arange(len(column)), column)),
            shape=sample.shape,
        ).tocsr()
        low_mass, high_mass = map(float, sample_bounds)
        edges = [
            2*low_mass*left-sample, sample-2*high_mass*left,
            sample_tagged-2*float(shadow_bound)*left,
        ]
        if simple_bound:
            edges.append(sample-sample_tagged-2*float(simple_bound)*left)
        if lower or upper != 1:
            edges.extend((float(lower)*sample-sample_tagged,
                          sample_tagged-float(upper)*sample))
        d = vstack((d, *edges), format="csr")
    if local_beta:
        meta = dict(np.load(cache.with_suffix(".local_ore_meta.npz")))
        column = meta["parents"]
        q1, q2, simple_extension, extra_extension = [
            load_npz(cache.with_suffix(f".{name}.npz"))
            for name in ("q_first", "q_second", "plain_ext", "parallel_ext")
        ]
        base = coo_matrix(
            (data["aut_count"][column], (np.arange(len(column)), column)),
            shape=q1.shape,
        ).tocsr()
        total = 2 if max_degree else 1
        square = total**2*base-2*total*q1+q2
        d = vstack((
            d,
            simple_extension+extra_extension-float(local_beta)*square,
            simple_extension-(273323/10**6)*square,
            extra_extension-square/4,
        ), format="csr")
    if blend:
        from multigraph_blend_moments import degree_moment_rows

        assert max_degree and sample_bounds
        expressions, extra_psd = degree_moment_rows(data, *sample_bounds)
        d = vstack((d, *(sum(float(factor)*row for factor, row in expression)
                         for expression in expressions)), format="csr")
    if method == "lp":
        r = linprog(
            -objective, A_ub=d, b_ub=np.zeros(d.shape[0]),
            A_eq=equality, b_eq=eq_rhs, bounds=(0, None),
            method="highs-ipm", options={"time_limit": seconds},
        )
        if r.success and output:
            np.savez(output, x=r.x, degree_multipliers=-r.ineqlin.marginals,
                     equality_multipliers=-r.eqlin.marginals)
        print(json.dumps({"status": r.message, "objective": -r.fun if r.success else None}, indent=2))
        return

    import scs
    gram = load_npz(cache.with_suffix(".gram.npz")).tocsc()
    block_record = json.loads(cache.with_suffix(".blocks.json").read_bytes())
    sizes = block_record["sizes"]
    variants = list(map(tuple, block_record["origins"]))
    mixed_origins = set()
    if mixed:
        more = json.loads(cache.with_suffix(".mixed_blocks.json").read_bytes())
        mixed_origins = set(map(tuple, more["origins"]))
        sizes.extend(more["sizes"])
        variants.extend([None]*len(more["sizes"]))
        gram = hstack((gram, load_npz(cache.with_suffix(".mixed_gram.npz"))), format="csc")
    if sample_bounds:
        extra_gram = load_npz(cache.with_suffix(".global_gram.npz"))
        gram = hstack((gram, extra_gram), format="csc")
        sizes.append(len(sample_meta["gram_flags"]))
        variants.append(None)
    left, right, weights, keep_sizes = [], [], [], []
    offset = 0
    for size, variant in zip(sizes, variants):
        if size > 1 and variant not in mixed_origins:
            for j in range(size):
                for i in range(j, size):
                    left.append(offset+i*size+j)
                    right.append(offset+j*size+i)
                    weights.append(1.0 if i == j else np.sqrt(2))
            keep_sizes.append(size)
        offset += size*size
    left, right, weights = np.asarray(left), np.asarray(right), np.asarray(weights)
    packed = ((gram[:, left]+gram[:, right]).multiply(weights/2)).T.tocsr()
    if with_ratio_psd:
        o0, o1, o2 = channels
        packed = vstack((packed, csr_matrix(np.array([o0, o1/np.sqrt(2), o2]))), format="csr")
        keep_sizes.append(2)
    if blend:
        for matrix, size in extra_psd:
            row, col = np.tril_indices(size)
            ordered = np.lexsort((row, col))
            row, col = row[ordered], col[ordered]
            sym = matrix[:, row*size+col]+matrix[:, col*size+row]
            scaled = sym.multiply(np.where(row == col, 0.5, np.sqrt(2)/2))
            packed = vstack((packed, scaled.T), format="csr")
            keep_sizes.append(size)
    a = vstack((equality, d, -eye(len(objective)), -packed), format="csc")
    b = np.r_[eq_rhs, np.zeros(a.shape[0]-len(eq_rhs))]
    cone = dict(z=len(eq_rhs), l=d.shape[0]+len(objective), s=keep_sizes)
    print(json.dumps({"shapes": list(a.shape), "nnz": a.nnz, "psd_blocks": len(keep_sizes)}), flush=True)
    optimizer = scs.SCS(
        dict(A=a, b=b, c=-objective), cone,
        linear_solver="cpu_indirect" if method == "indirect" else "qdldl",
        eps_abs=1e-7, eps_rel=1e-7, max_iters=iterations, time_limit_secs=seconds,
        verbose=True,
    )
    warm = lower == 0 and (not sample_bounds or sample_bounds[0] <= target <= sample_bounds[1])
    x0 = (pentagon_seed(data) if max_degree else red_biclique_seed(data)) if warm else None
    if x0 is not None:
        assert abs(float(objective @ x0)-float(target)) < 1e-12
        assert float(np.max(d @ x0)) < 1e-12
        assert float(np.max(np.abs(equality @ x0-eq_rhs))) < 1e-12
    solution = optimizer.solve(warm_start=x0 is not None, x=x0)
    if output:
        np.savez(output, **{key: solution[key] for key in ("x", "y", "s")})
    print(json.dumps(solution["info"], indent=2), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("cache", type=Path)
    parser.add_argument("--vendor", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--method", choices=("lp", "direct", "indirect"), default="direct")
    parser.add_argument("--seconds", type=int, default=160)
    parser.add_argument("--iterations", type=int, default=8000)
    parser.add_argument("--lower", type=Fraction, default=Fraction(0))
    parser.add_argument("--upper", type=Fraction, default=Fraction(1))
    parser.add_argument("--simple-bound", type=Fraction)
    parser.add_argument("--no-caps", action="store_true")
    parser.add_argument("--no-ratio-psd", action="store_true")
    parser.add_argument("--sample", nargs=2, type=Fraction, metavar=("MASS_LO", "MASS_HI"))
    parser.add_argument("--mixed", action="store_true")
    parser.add_argument("--local-beta", type=Fraction)
    parser.add_argument("--blend", action="store_true")
    args = parser.parse_args()
    if args.vendor:
        sys.path.insert(0, str(args.vendor))
    assert 0 <= args.lower <= args.upper <= 1
    assert not args.sample or 0 <= args.sample[0] <= args.sample[1]
    solve(args.cache, args.output, args.method, args.seconds, args.iterations,
          args.lower, args.upper, args.simple_bound, not args.no_caps, not args.no_ratio_psd,
          args.sample, args.mixed, args.local_beta, args.blend)


if __name__ == "__main__":
    main()
