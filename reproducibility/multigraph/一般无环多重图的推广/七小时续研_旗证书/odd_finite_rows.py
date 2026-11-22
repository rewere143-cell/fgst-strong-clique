"""Finite-degree and weighted anchor rows for the parity model."""
from fractions import Fraction as F
from functools import cache
from math import ceil, comb, factorial, floor
import json

from half_anchor_flag import CACHE
from k5_turan_rows import clique_repeat_rows, triangle_signature_rows
from multigraph_low_repeat_search import enhanced_system
from multigraph_weighted_maxdeg_exact import verify


@cache
def old_cycle_implication():
    """Recover M <= B+nu Z_C from the archived no-red-pentagon dual."""
    import numpy as np

    old = CACHE.parent / "absence_c5_mass_98_81.json"
    certificate = json.loads(old.read_bytes())
    settings = certificate["settings"]
    assert F(settings["mass_low"]) == F(98, 81)
    assert F(settings["e_low"]) == 0 and F(settings["e_high"]) == F(32, 81)
    assert F(settings["mass_high"]) >= F(5, 4)
    system = enhanced_system(CACHE, settings)
    _, iq, _, _, data, _, scale, _, _ = system
    cycle = (data["order"] == 5) & (data["code"] == 6012)
    row = iq.shape[0]-1
    assert np.array_equal(iq[row].toarray().ravel(), scale*cycle)
    multiplier = F(certificate["inequalities"][row], certificate["linear_denominator"])
    assert multiplier > 0
    exact = verify(CACHE, certificate, system)
    assert exact["mode"] == "bound"
    return F(exact["rational_bound"]), multiplier


def finite_clique_rows(data, mlo, degree_high):
    """Reinstate the discarded finite term in each pure red-clique repeat row."""
    rows = clique_repeat_rows(data, mlo, include_losses=True)
    output = []
    previous = None
    for (one, extension), (constant, parent) in rows:
        key = tuple(parent.indices)
        k = int(data["order"][key[0]])
        if key != previous:
            penalty = F(1 if k == 2 else k, degree_high)
            if k == 4:
                penalty += F(6, degree_high**2)
            # Rounding removes arbitrary degree-window denominators.
            penalty = F(floor(1000*penalty), 1000)
            constant += penalty
        output.append(((one, extension), (constant, parent)))
        previous = key
    return output


def finite_triangle_rows(data, mlo, degree_high, grid=100):
    """Use 2(D−1)−p rather than 2D−p in the local Ore bound."""
    rows = triangle_signature_rows(data, mlo, stronger=True)
    assert len(rows) == 24 and degree_high >= 3
    beta = F(1489, 5000)
    b = F(ceil(grid*(2-F(2, degree_high))), grid)
    # A lower red-spoke defect follows from a monotone quadratic.
    def polynomial(u):
        return 3*beta*(b-1)**2 + (F(1, 2)+2*beta*(b-1))*u + beta*u*u

    lo, hi = 0, 10001
    while hi-lo > 1:
        mid = (lo+hi)//2
        if polynomial(F(mid, 10000)) <= mlo:
            lo = mid
        else:
            hi = mid
    defect = F(lo, 10000)
    output = []
    for block in range(0, len(rows), 8):
        for kind, row in enumerate(rows[block:block+8]):
            items = list(row)
            if kind in (0, 1):
                items[0] = (mlo-F(309, 250)*(b/2)**2, items[0][1])
                items[2] = (-2*beta*b, items[2][1])
            elif kind == 2:
                items[1] = (defect-3, items[1][1])
            elif kind == 3:
                items[0] = (mlo-3*beta*b*b, items[0][1])
                items[2] = (2*beta*b, items[2][1])
            elif kind == 4:
                items[0] = (3*(mlo-beta*b*b), items[0][1])
                items[3] = (2*beta*b, items[3][1])
            elif kind in (5, 6):
                items[0] = (mlo-F(1233, 1000)*(b/2)**2, items[0][1])
            else:
                bonus = F(floor(F(30000, degree_high**2)), 10000)
                items[0] = (items[0][0]+bonus, items[0][1])
            output.append(tuple(items))
    return output


def independent_sample_parts(data, want_sixth):
    """Return parent and independent edge extensions in each retained model."""
    import numpy as np
    from scipy.sparse import coo_matrix, csr_matrix, hstack, load_npz

    n = len(data["order"])
    def parent_matrix(parents, weights):
        return coo_matrix((weights.astype(np.int64), (np.arange(len(parents)), parents)),
                          shape=(len(parents), n), dtype=np.int64).tocsr()

    parents = np.load(CACHE.with_suffix(".sample_meta.npz"))["extension_parents"]
    sample = load_npz(CACHE.with_suffix(".sample.npz")).astype(np.int64)
    tagged = load_npz(CACHE.with_suffix(".sample_tagged.npz")).astype(np.int64)
    n5 = sample.shape[1]
    assert np.all(data["order"][:n5] <= 5) and not np.any(data["order"][n5:] <= 5)
    pad = csr_matrix((sample.shape[0], n-n5), dtype=np.int64)
    p5 = parent_matrix(parents, data["aut_count"][parents])
    p6 = first6 = None
    if want_sixth:
        from half_anchor_shadow import SHADOW

        # All order-four untagged parents have a complete simple-edge
        # projection onto the sixth-order shadow.
        source6 = np.load(SHADOW.with_suffix(".data.npz"))
        parents6 = np.load(SHADOW.with_suffix(".sample_meta.npz"))["extension_parents"]
        plain = (source6["order"][parents6] == 4) & (source6["mask"][parents6] == 0)
        lookup = {tuple(map(int, triple)): i for i, triple in enumerate(
            zip(source6["order"], source6["code"], source6["mask"])
        )}
        columns = [lookup[tuple(map(int, triple))] for triple in
                   zip(data["order"], data["code"], data["mask"])]
        inverse = {column: i for i, column in enumerate(columns)}
        new_parents = [inverse[int(column)] for column in parents6[plain]]
        sample6 = (load_npz(SHADOW.with_suffix(".sample.npz")) -
                   load_npz(SHADOW.with_suffix(".sample_tagged.npz"))).tocsr()[plain]
        assert sample6.nnz == sample6[:, columns].nnz
        p6 = parent_matrix(new_parents, data["aut_count"][new_parents])
        first6 = sample6[:, columns].astype(np.int64)
    return p5, hstack([sample, pad]), hstack([tagged, pad]), p6, first6


def fixed_finite_sampling(data, scale, degree, repeats=None):
    """Exact independent-edge identities for fixed integer m and, optionally, repeats."""
    import numpy as np
    from scipy.sparse import csr_matrix, vstack

    assert degree >= 9 and degree % 2 == 1 and (repeats is None or repeats >= 1)
    mass = degree**2 + (degree//2)**2 + 1
    d2 = degree**2
    if repeats is not None:
        assert repeats <= mass

    def scale_equations(a, p, total):
        # Whole linear equations may be rescaled by any positive factor.
        divisor = max(d2, 2*total)
        multiplier = max(1, scale//divisor)
        return (d2*a-2*total*p)*multiplier

    p5, sample, tagged, p6, first6 = independent_sample_parts(data, repeats is not None)
    fixed = [scale_equations(sample, p5, mass)]
    if repeats is not None:
        fixed.append(scale_equations(tagged, p5, repeats))
        q1 = csr_matrix(np.where((data["order"] == 2) & (data["mask"] != 0), 2, 0)).astype(np.int64)
        norm = csr_matrix(data["normalizer"].astype(np.int64))
        fixed.append((mass*q1-repeats*norm)*max(1, scale//mass))
        fixed.append(scale_equations(first6, p6, mass-repeats))
    return vstack(fixed, format="csr")


def tight_sample_caps(data, scale, mass_high, support_cap, extra_cap):
    """Restrict every independent-edge sample to the active mass box."""
    from scipy.sparse import vstack

    def upper(a, p, bound):
        rhs = 2*F(bound)
        multiplier = max(1, scale//max(abs(rhs.numerator), rhs.denominator))
        return (rhs.denominator*a-rhs.numerator*p)*multiplier

    p5, sample, tagged, p6, first6 = independent_sample_parts(data, True)
    return vstack((upper(sample, p5, mass_high),
                   upper(tagged, p5, extra_cap),
                   upper(sample-tagged, p5, support_cap),
                   upper(first6, p6, support_cap)), format="csr")


def d9_marked_vertex_floor(data, scale, vertices):
    """A degree-four polynomial majorant of the marked-vertex indicator."""
    import numpy as np
    from scipy.sparse import csr_matrix
    from multigraph_lift_probe import decode, edge_pairs

    @cache
    def star(first, extra):
        order = 1+first+extra
        assert 2 <= order <= 5 and extra <= 2
        pairs = tuple(edge_pairs(order))
        centers = [tuple(i for i, pair in enumerate(pairs) if center in pair)
                   for center in range(order)]
        out = np.zeros(len(data["order"]), dtype=np.int64)
        for row in np.flatnonzero(data["order"] == order):
            mask = int(data["mask"][row])
            if mask.bit_count() != extra:
                continue
            colors = decode(order, int(data["code"][row]))
            for incident in centers:
                if all(colors[i] == 2 for i in incident) and not mask & ~sum(1 << i for i in incident):
                    out[row] += factorial(first)*factorial(extra)
        return csr_matrix(out)*9**(order-2)

    polynomial = csr_matrix((1, len(data["order"])), dtype=np.int64)
    for degree, coefficient in enumerate((695, -215, 25, -1), start=1):
        # Each monomial uses h=h_s+j, with j in {0,1,2}.
        terms = star(degree, 0)
        for extra in range(1, degree+1):
            first = degree-extra
            second = 2**(extra-1)-1
            contribution = (1-second)*star(first, 1)
            if second:
                contribution += second*star(first, 2)
            terms = terms + comb(degree, extra)*contribution
        polynomial += coefficient*terms
    norm = csr_matrix(data["normalizer"].astype(np.int64))
    row = 504*vertices*norm-196*polynomial
    largest = int(np.max(np.abs(row.data)))
    return row*max(1, scale//largest)


def finite_root_union_rows(data, degree_low, degree_high):
    """Bound the combined repeat degree and common neighborhood on a red root."""
    import numpy as np
    from scipy.sparse import csr_matrix
    from multigraph_lift_probe import decode, edge_pairs

    assert 9 <= degree_low <= degree_high and degree_low % 2 == degree_high % 2 == 1
    n = len(data["order"])
    compound = np.zeros((2, n), dtype=np.int64)
    pairs = tuple(edge_pairs(3))
    for row in np.flatnonzero(data["order"] == 3):
        colors = decode(3, int(data["code"][row]))
        mask = int(data["mask"][row])
        for root in range(3):
            if colors[root] != 2:
                continue
            root_tag = (mask >> root)&1
            remaining = mask & ~(1 << root)
            if remaining.bit_count() == 1:
                # The other tag is a repeat neighbor of one root endpoint.
                compound[root_tag, row] += 1
            elif not remaining and all(colors[i] > 0 for i in range(3) if i != root):
                compound[root_tag, row] += 1
    rows = []
    for root_tag in (0, 1):
        upper = max(
            F(2*d-2-ceil(F(d*d+(d//2)**2+1-2*d+1+root_tag, d-1)), d)
            for d in range(degree_low, degree_high+1, 2)
        )
        upper = F(ceil(10000*upper), 10000)
        parent = csr_matrix(((data["order"] == 2)&((data["mask"] != 0) == bool(root_tag))).astype(np.int64))
        rows.append(((F(1), csr_matrix(compound[root_tag])), (-upper, parent)))
    return rows
