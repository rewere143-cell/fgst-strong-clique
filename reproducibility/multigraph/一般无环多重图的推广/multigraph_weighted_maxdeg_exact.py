"""Rational replay for upper bounds and exclusions in the weighted flag model."""

import argparse
from collections import defaultdict
from fractions import Fraction as Q
import hashlib
import json
from math import comb, factorial, lcm
from pathlib import Path
import sys

from multigraph_weighted_ore_solve import local_defect


CHANNELS = ("q_first", "q_second", "plain_ext", "parallel_ext")
SUFFIXES = (
    ".data.npz", ".ore.npz", ".blocks.json", ".gram.npz", ".mixed_blocks.json",
    ".mixed_gram.npz", ".sample_meta.npz", ".sample.npz", ".sample_tagged.npz",
    ".global_gram.npz", ".local_ore_meta.npz",
) + tuple(f".{x}.npz" for x in CHANNELS)


def source_hashes(cache):
    return {suffix: hashlib.sha256(cache.with_suffix(suffix).read_bytes()).hexdigest()
            for suffix in SUFFIXES}


def gap_by_tag(n, k):
    choices = comb(n-2, k-1) if k else 1
    return Q(n**(n-3)*choices, max(1, k)*factorial(n-2))


def build_integer(cache, settings):
    import numpy as np
    from scipy.sparse import coo_matrix, csr_matrix, hstack, load_npz, vstack

    data = dict(np.load(cache.with_suffix(".data.npz")))
    assert data["max_degree"]
    tags = np.asarray([int(mask).bit_count() for mask in data["mask"]], dtype=np.int8)
    order = data["order"]
    n = len(order)
    norm = csr_matrix(data["normalizer"].astype(np.int64))
    rq0 = csr_matrix(np.where((order == 2) & (tags == 0), 2, 0))
    rq1 = csr_matrix(np.where((order == 2) & (tags == 1), 2, 0))
    q0 = int(rq0.indices[0])
    q1 = int(rq1.indices[0])
    obj = csr_matrix(data["twice_obj"].astype(np.int64))
    o0, o1, o2 = [csr_matrix((tags == k)*data["twice_obj"].astype(np.int64)) for k in range(3)]
    degree = load_npz(cache.with_suffix(".ore.npz")).astype(np.int64)
    equality = vstack((norm, degree), format="csr")
    simple = Q(settings.get("counterexample_support_cap") or Q(5, 4))
    assert Q(12333, 10000) <= simple <= Q(5, 4)
    lo, hi = map(Q, (settings["e_low"], settings["e_high"]))
    mlo, mhi = map(Q, (settings["mass_low"], settings["mass_high"]))
    assert 0 <= lo <= hi <= 1 and 1 <= mlo <= mhi
    # A caller may establish the support cap directly, independently of mlo.
    assert simple == Q(5, 4) or mlo >= Q(5, 4) or settings.get("known_support_and_anchor_bounds") is True
    extra = mlo-mlo*mlo/2
    local = Q(settings["local_beta"])
    # See 二部标记见证亏损与邻域差.md for the exact interval proof.
    assert local >= Q(2973, 10000)

    expressions = []

    def add(*terms):
        expressions.append(tuple((Q(c), a) for c, a in terms))

    add((Q(1, 2), o2), (Q(1, 4), o1), (-extra, norm))
    add((Q(1, 2), o2), (-extra, rq1))
    add((Q(1, 4), o1), (-extra, rq0))
    add((Q(1, 2), o0), (Q(1, 4), o1), (-simple, norm))
    add((Q(1, 2), o0), (-simple, rq0))
    add((Q(1, 4), o1), (-simple, rq1))
    defect = csr_matrix(local_defect(data).astype(np.int64))
    add((Q(1, 2), o0), (Q(9, 20), defect), (Q(-5, 4), rq0))
    if lo or hi != 1:
        add((lo, norm), (-1, rq1))
        add((1, rq1), (-hi, norm))
        endpoints = (2*lo*(1-lo), 2*hi*(1-hi))
        bounds = (
            ((1-hi)**2, (1-lo)**2),
            (min(endpoints), Q(1, 2) if lo <= Q(1, 2) <= hi else max(endpoints)),
            (lo**2, hi**2),
        )
        for (lower, upper), channel in zip(bounds, (o0, o1, o2)):
            add((lower/2, obj), (Q(-1, 2), channel))
            add((Q(1, 2), channel), (-upper/2, obj))
    for order_value in range(3, int(max(order))+1):
        for k in range(order_value):
            group = ((order == order_value) & (tags == k))
            if not group.any():
                continue
            add((1, csr_matrix(group.astype(np.int64))),
                (-gap_by_tag(order_value, k), rq1 if k else rq0))

    def unit_parents(indices, shape):
        return coo_matrix(
            (data["aut_count"][indices], (np.arange(len(indices)), indices)),
            shape=shape, dtype=np.int64,
        ).tocsr()

    sample_info = dict(np.load(cache.with_suffix(".sample_meta.npz")))
    sample = load_npz(cache.with_suffix(".sample.npz")).astype(np.int64)
    sample_tag = load_npz(cache.with_suffix(".sample_tagged.npz")).astype(np.int64)
    left = unit_parents(sample_info["extension_parents"], sample.shape)
    add((2*mlo, left), (-1, sample))
    add((1, sample), (-2*mhi, left))
    add((1, sample_tag), (-2*extra, left))
    add((1, sample), (-1, sample_tag), (-2*simple, left))
    if lo or hi != 1:
        add((lo, sample), (-1, sample_tag))
        add((1, sample_tag), (-hi, sample))

    local_info = np.load(cache.with_suffix(".local_ore_meta.npz"))
    first, second, plain, tagged = [
        load_npz(cache.with_suffix(f".{name}.npz")).astype(np.int64) for name in CHANNELS
    ]
    local_base = unit_parents(local_info["parents"], first.shape)
    square = 4*local_base-4*first+second
    add((1, plain), (1, tagged), (-local, square))
    add((1, plain), (-Q(273323, 10**6), square))
    add((1, tagged), (-Q(1, 4), square))

    extra_psd = []
    if settings.get("blend"):
        from multigraph_blend_moments import degree_moment_rows

        rows, extra_psd = degree_moment_rows(data, mlo, mhi)
        expressions.extend(rows)
    if settings.get("ore_loss"):
        from multigraph_local_ore_loss import local_ore_loss_rows

        assert max(order) >= 5
        expressions.extend(local_ore_loss_rows(data, local))
    if settings.get("pentagon") or settings.get("abundance"):
        index = np.flatnonzero((order == 5) & (tags == 0) & (data["code"] == 6012))
        assert len(index) == 1 and data["aut_count"][index[0]] == 10
        cycle = csr_matrix(([10], ([0], index)), shape=(1, n), dtype=np.int64)
        if settings.get("pentagon"):
            from multigraph_low_repeat_search import rooted_pentagon_rows

            expressions.extend(rooted_pentagon_rows(data, cycle, rq0))
        if settings.get("abundance"):
            gamma, eps = Q(99999, 100000), Q(1, 500000000)
            add((Q(1, 2), o0), (-gamma, cycle), (-(Q(5, 4)-gamma/8+eps), rq0))
    multiplicity = settings.get("multiplicity")
    cut_path = settings.get("orientation_cuts")
    assert not (multiplicity is not None and cut_path)
    if multiplicity is not None:
        from multigraph_bounded_multiplicity import capped_tag_rows

        add((1, capped_tag_rows(data, multiplicity)))
    if cut_path:
        from multigraph_orientation_cuts import OUTPUT_SCALE, replay_file

        path = cache.parent/cut_path
        assert hashlib.sha256(path.read_bytes()).hexdigest() == settings["orientation_sha256"]
        add((Q(1, OUTPUT_SCALE), replay_file(path, settings)))
    if settings.get("ratio"):
        add(((1-lo-hi)/2, o2), (-(lo+hi)/4, o1), (lo*hi/2, obj))
    denominators = [c.denominator for group in expressions for c, _ in group]
    sample_categories = settings.get("sample_psd")
    sample_caps = (min(simple, (1-lo)*mhi), min(extra, hi*mhi))
    if sample_categories:
        from multigraph_sample_gram import model_hashes, model_blocks

        assert all(type(i) is int and 0 <= i < 4 for i in sample_categories)
        assert model_hashes(cache) == settings["sample_psd_hashes"]
        denominators.extend((2*cap).denominator for cap in sample_caps)
    local_gram = settings.get("ore_sample_psd")
    degree_gram = settings.get("degree_psd")
    if local_gram or degree_gram:
        from multigraph_local_sample_psd import hashes, blocks as local_blocks, degree_blocks

        assert hashes(cache) == settings["ore_sample_psd_hashes"]
        assert all(type(i) is int and 0 <= i < 4 for i in (local_gram or [])+(degree_gram or []))
    scale = lcm(4, *denominators, mlo.numerator if settings.get("ratio") else 1)
    inequalities = vstack([
        sum(int(c*scale)*a for c, a in group) for group in expressions
    ], format="csr")
    equality = equality*scale

    block_record = json.loads(cache.with_suffix(".blocks.json").read_bytes())
    gram = load_npz(cache.with_suffix(".gram.npz")).tocsc().astype(np.int64)
    mixed_record = json.loads(cache.with_suffix(".mixed_blocks.json").read_bytes())
    mixed = load_npz(cache.with_suffix(".mixed_gram.npz")).tocsc().astype(np.int64)
    used_mixed = set(map(tuple, mixed_record["origins"]))
    full, sizes = [], []
    at = 0
    for size, key in zip(block_record["sizes"], block_record["origins"]):
        if size > 1 and tuple(key) not in used_mixed:
            full.append(gram[:, at:at+size**2]*scale)
            sizes.append(size)
        at += size**2
    at = 0
    for size in mixed_record["sizes"]:
        if size > 1:
            full.append(mixed[:, at:at+size**2]*scale)
            sizes.append(size)
        at += size**2
    global_gram = load_npz(cache.with_suffix(".global_gram.npz")).astype(np.int64)
    full.append(global_gram*scale)
    sizes.append(len(sample_info["gram_flags"]))
    full.append(hstack((o0.T*(scale//2), o1.T*(scale//4),
                       o1.T*(scale//4), o2.T*(scale//2)), format="csc"))
    sizes.append(2)
    for matrix, size in extra_psd:
        full.append(matrix*scale)
        sizes.append(size)
    if settings.get("ratio"):
        full.append(hstack((
            o0.T*(scale//2), o1.T*(scale//4), rq0.T*scale,
            o1.T*(scale//4), o2.T*(scale//2), rq1.T*scale,
            rq0.T*scale, rq1.T*scale, norm.T*int(scale/mlo),
        ), format="csc"))
        sizes.append(3)
    if sample_categories:
        for block, size in model_blocks(cache, sample_caps, scale, sample_categories):
            full.append(block)
            sizes.append(size)
    neighbor_categories = settings.get("neighbor_psd")
    if neighbor_categories:
        from multigraph_neighbor_sample_gram import blocks, hashes

        assert all(type(i) is int and 0 <= i < 4 for i in neighbor_categories)
        assert hashes(cache) == settings["neighbor_psd_hashes"]
        for block, size in blocks(cache, scale, neighbor_categories):
            full.append(block)
            sizes.append(size)
    for flags, builder in ((degree_gram, degree_blocks), (local_gram, local_blocks)) if (local_gram or degree_gram) else ():
        if flags:
            for block, size in builder(cache, scale, flags):
                full.append(block)
                sizes.append(size)
    support_gram = settings.get("support_degree_psd")
    if support_gram:
        from multigraph_local_sample_psd import support_hashes, support_blocks

        assert all(type(i) is int and 0 <= i < 4 for i in support_gram)
        assert support_hashes(cache) == settings["support_degree_psd_hashes"]
        for block, size in support_blocks(cache, scale, support_gram):
            full.append(block)
            sizes.append(size)
    system = (equality, inequalities, full, sizes, data, tags, scale,
              np.asarray(obj.toarray()).ravel(), (q0, q1))
    if settings.get("orientation_full"):
        from multigraph_full_orientation import extend_integer

        assert multiplicity is None
        system = extend_integer(cache.parent/settings["orientation_full"], settings, system)
    return system


def rounded_certificate(cache, solution_path, mode, settings, system):
    import numpy as np

    equality, inequalities, full, sizes, data, _, _, _, _ = system
    raw = np.load(solution_path)["y"]
    n_eq, n_ineq = equality.shape[0], inequalities.shape[0]
    dim = len(data["order"])
    pos = n_eq+n_ineq+dim
    lden, vden = 10**12, 10**9
    eq = [round(float(val)*lden) for val in raw[:n_eq]]
    ineq = [max(0, round(float(val)*lden)) for val in raw[n_eq:n_eq+n_ineq]]
    grams = []
    for size in sizes:
        triangle = np.tril_indices(size)
        take = np.lexsort((triangle[0], triangle[1]))
        row, col = triangle[0][take], triangle[1][take]
        mat = np.zeros((size, size))
        entries = raw[pos:pos+len(row)]/np.where(row == col, 1, np.sqrt(2))
        mat[row, col] = entries
        mat[col, row] = entries
        values, vectors = np.linalg.eigh(mat)
        block = []
        for i in np.flatnonzero(values > 0):
            vector = [round(float(v) * np.sqrt(values[i])*vden) for v in vectors[:, i]]
            if any(vector):
                block.append(vector)
        grams.append(block)
        pos += len(row)
    assert pos == len(raw)
    return {
        "model_sha256": source_hashes(cache), "mode": mode, "settings": settings,
        "linear_denominator": lden, "vector_denominator": vden,
        "equalities": eq, "inequalities": ineq, "gram_squared_vectors": grams,
    }


def verify(cache, certificate, expected_system=None):
    assert source_hashes(cache) == certificate["model_sha256"]
    system = expected_system or build_integer(cache, certificate["settings"])
    equality, inequalities, grams, sizes, data, tags, scale, objective, _ = system
    lden = certificate["linear_denominator"]
    vden = certificate["vector_denominator"]
    assert lden > 0 and vden > 0
    denom_multiplier = lcm(lden, vden*vden, 2)
    denote = scale*denom_multiplier
    exact = [0]*len(tags)

    def accumulate(matrix, multipliers, factor):
        matrix = matrix.tocsr()
        assert len(multipliers) == matrix.shape[0]
        for i, value in enumerate(multipliers):
            if not value:
                continue
            multiplier = value*factor
            start, end = matrix.indptr[i:i+2]
            for j, coeff in zip(matrix.indices[start:end], matrix.data[start:end]):
                exact[j] += multiplier*int(coeff)

    eq = certificate["equalities"]
    iq = certificate["inequalities"]
    assert all(isinstance(v, int) for v in eq)
    assert all(isinstance(v, int) and v >= 0 for v in iq)
    accumulate(equality, eq, denom_multiplier//lden)
    accumulate(inequalities, iq, denom_multiplier//lden)
    factors = certificate["gram_squared_vectors"]
    assert len(factors) == len(sizes)
    for matrix, size, vectors in zip(grams, sizes, factors):
        packed = [0]*(size*size)
        for vector in vectors:
            assert len(vector) == size and all(isinstance(v, int) for v in vector)
            for i, x in enumerate(vector):
                for j, y in enumerate(vector):
                    packed[i*size+j] += x*y
        accumulate(matrix.T, packed, -denom_multiplier//(vden*vden))
    if certificate["mode"] == "bound":
        exact = [value-int(obj)*(denote//2) for value, obj in zip(exact, objective)]
    else:
        assert certificate["mode"] == "infeasible"

    orientation_size = 0
    if "orientation_owner" in data:
        at = data["orientation_offset"]
        orientation_size = len(exact)-at
        curve = defaultdict(int)
        for base, coefficient in zip(map(int, data["orientation_owner"]), exact[at:]):
            curve[base] = max(curve[base], -coefficient)
        exact = exact[:at]
        for base, loss in curve.items():
            exact[base] -= loss

    maximum = defaultdict(int)
    sum_individual = defaultdict(Q)
    for n, k, aut, r in zip(data["order"], tags, data["aut_count"], exact):
        if r < 0:
            key = (int(n), int(k))
            maximum[key] = max(maximum[key], -r)
            sum_individual[key] += Q(-r, int(aut))
    cost = [Q(0), Q(0)]
    for (n, k), worst in maximum.items():
        raw = Q(worst, 2) if n == 2 else gap_by_tag(n, k)*worst
        cost[int(k > 0)] += min(raw, sum_individual[n, k])/denote
    lo, hi = (Q(certificate["settings"][key]) for key in ("e_low", "e_high"))
    correction = max((1-e)*cost[0]+e*cost[1] for e in (lo, hi))
    constant = Q(eq[0], lden)
    result = {
        "mode": certificate["mode"], "raw_bound": str(constant),
        "correction": str(correction), "rational_bound": str(constant+correction),
        "decimal_bound": float(constant+correction),
        "coefficient_rows": len(exact), "negative_rows": sum(v < 0 for v in exact),
        "rigorous_infeasible": certificate["mode"] == "infeasible" and constant+correction < 0,
    }
    if orientation_size:
        result["orientation_rows"] = orientation_size
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("cache", type=Path)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("--vendor", type=Path)
    parser.add_argument("--round", type=Path)
    parser.add_argument("--mode", choices=("bound", "infeasible"), default="infeasible")
    parser.add_argument("--lower", default="1/4")
    parser.add_argument("--upper", default="3/8")
    parser.add_argument("--mass-low", default="5/4")
    parser.add_argument("--mass-high", default="3/2")
    parser.add_argument("--local-beta", default="239/800")
    parser.add_argument("--blend", action="store_true")
    parser.add_argument("--solver-settings", type=Path)
    args = parser.parse_args()
    if args.vendor:
        sys.path.insert(0, str(args.vendor))
    if args.round:
        settings = dict(e_low=args.lower, e_high=args.upper, mass_low=args.mass_low,
                        mass_high=args.mass_high, local_beta=args.local_beta)
        if args.blend:
            settings["blend"] = True
        if args.solver_settings:
            settings = json.loads(args.solver_settings.read_bytes())
        system = build_integer(args.cache, settings)
        certificate = rounded_certificate(args.cache, args.round, args.mode, settings, system)
        result = verify(args.cache, certificate, system)
        certificate["replay_result"] = result
        args.certificate.write_text(json.dumps(certificate, separators=(",", ":"))+"\n",
                                    encoding="utf-8")
    else:
        certificate = json.loads(args.certificate.read_bytes())
        result = verify(args.cache, certificate)
        assert result == certificate["replay_result"]
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
