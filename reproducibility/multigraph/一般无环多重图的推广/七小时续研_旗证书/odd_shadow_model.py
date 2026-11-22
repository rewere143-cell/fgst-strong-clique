"""Exact parity counterexample rows with separate lower anchor and upper support bounds."""
from fractions import Fraction as F
from math import ceil, floor, lcm
from pathlib import Path
import sys


HERE = Path(__file__).resolve().parent
PREVIOUS = HERE.parent / "三小时续研_旗证书"
sys.path.insert(0, str(PREVIOUS))

from half_anchor_flag import CACHE, restrict_zero_coordinates
from half_anchor_projection import ABUNDANCE, ANCHOR, CONDITIONAL, UNIFORM, maximum_support
from half_anchor_shadow import SHADOW
from k5_turan_rows import (
    clique_repeat_rows, common_neighbor_rows, contains_red_clique, contains_red_k5, triangle_signature_rows,
)
from finite_neighbor_rows import weighted_mantel_rows
from multigraph_six_shadow_search import anchor_six_coefficients, build_shadow, decorated_anchors
from multigraph_weighted_maxdeg_exact import gap_by_tag
from odd_finite_rows import (
    d9_marked_vertex_floor, finite_clique_rows, finite_root_union_rows, finite_triangle_rows, fixed_finite_sampling,
    old_cycle_implication, tight_sample_caps,
)


def projection_rows(alpha, direct_gamma):
    _, abundance, abundance_error = ABUNDANCE
    _, anchor, anchor_error = ANCHOR
    _, conditional, conditional_error, theta = CONDITIONAL
    return [
        (UNIFORM, F(0)),
        (UNIFORM-abundance/8+abundance_error, -abundance),
        (UNIFORM+anchor_error, alpha*anchor),
        (UNIFORM-theta*conditional/8+conditional_error, (alpha-theta)*conditional),
        (UNIFORM-direct_gamma/16+F(1, 500000000), (alpha-F(1, 2))*direct_gamma),
    ]


def support_bound(settings):
    """An independently valid support cap may improve the projected envelope."""
    alpha = F(settings["parity_anchor_minimum"])
    assert 0 <= alpha <= 5
    if alpha:
        projected, _ = maximum_support(projection_rows(alpha, F(settings["direct_gamma"])))
    else:
        projected = UNIFORM
    cap = min(projected, F(settings.get("parity_support_cap", UNIFORM)))
    assert 0 < cap <= UNIFORM
    return cap


def repeat_line(alpha, delta):
    """Return slope and intercept in the valid affine upper bound j <= slope*r+const."""
    assert 0 <= delta <= F(1, 10)
    if alpha >= 1:
        return F(1, 2), 2*delta
    if alpha <= F(1, 2):
        left = 4*delta
    else:
        left = (alpha*(alpha-F(1, 2))*(1+alpha)+2*delta*(2+alpha))/(1+alpha*alpha)
    right = F(1, 2)+2*delta
    slope = max(F(1, 2), (right-left)/(1-alpha))
    return F(ceil(slope*100000), 100000), F(ceil((left-slope*alpha)*100000), 100000)


def build_odd_system(settings):
    import numpy as np
    from scipy.sparse import csr_matrix, vstack

    mlo, mhi, elo, ehi, alpha = (F(settings[key]) for key in
        ("mass_low", "mass_high", "e_low", "e_high", "parity_anchor_minimum"))
    cap = F(ceil(support_bound(settings)*100000), 100000)
    assert F(23, 20) <= mlo <= mhi <= UNIFORM and 0 <= elo <= ehi <= 1
    assert settings.get("k5_free") and settings.get("k5_turan")
    assert settings.get("triangle_signatures_v2")
    base_cap = max(cap, F(12333, 10000))
    base_settings = dict(
        settings,
        known_support_and_anchor_bounds=True,
        counterexample_support_cap=str(base_cap),
        mass_high="128829/100000",
        simple_support_cap=str(base_cap),
        abundance_gamma="99999/100000",
        abundance_epsilon="1/500000000",
        rooted_pentagon=True,
        anchor_minimum=str(min(alpha, F(33, 100))),
        anchor_gamma="2841/5000",
        anchor_epsilon="1/1000000000",
        anchor_excess=True,
        shadow_blocks=settings.get("selected_shadow_blocks"),
    )
    eq, iq, grams, sizes, data, tags, scale, obj, roots = build_shadow(CACHE, SHADOW, base_settings)
    obj = obj.astype(np.int64)
    order = data["order"]
    root0 = csr_matrix(np.where((order == 2) & (tags == 0), 2, 0))
    root1 = csr_matrix(np.where((order == 2) & (tags == 1), 2, 0))
    norm = root0+root1
    o0 = csr_matrix(np.where(tags == 0, obj, 0))
    o1 = csr_matrix(np.where(tags == 1, obj, 0))
    rows = [
        ((F(1, 2), csr_matrix(obj)), (-mhi, norm)),
        ((F(1, 2), o0), (F(1, 4), o1), (-cap, norm)),
        ((F(1, 2), o0), (-cap, root0)),
        ((F(1, 4), o1), (-cap, root1)),
    ]
    for k in range(4):
        group = (order == 6) & (tags == k)
        if group.any():
            rows.append(((F(1), csr_matrix(group.astype(np.int64))),
                         (-gap_by_tag(6, k), root1 if k else root0)))

    depth = int(settings["anchor_tag_depth"])
    plain = (order == 6) & (tags == 0)
    anchors = {int(code): anchor_six_coefficients(int(code)) for code in data["code"][plain]}
    use, _, good, excess = decorated_anchors(data, plain, anchors, depth)
    assert not np.any((order == 6) & ~use)
    cycle = (order == 5) & (data["code"] == 6012)
    slope, const = repeat_line(alpha, UNIFORM-mlo)
    for k in range(depth+1):
        cycle_k = csr_matrix(np.where(cycle & (tags == k), 10, 0))
        loss = 5*cycle_k-csr_matrix(good[k])
        rows.extend((
            ((alpha, cycle_k), (-F(1), loss)),
            ((F(1), csr_matrix(excess[k])), (-const, cycle_k), (-slope, loss)),
        ))
        if k == 0:
            for _, gamma, eps, theta in (CONDITIONAL,
                                         (None, F(settings["direct_gamma"]), F(2, 10**9), F(1, 2))):
                rows.append(((F(1, 2), o0), (gamma, loss), (-theta*gamma, cycle_k),
                             (-UNIFORM+theta*gamma/8-eps, root0)))

    degree_high = settings.get("parity_degree_high")
    if degree_high:
        assert isinstance(degree_high, int) and degree_high >= 3
        rows.extend(finite_clique_rows(data, mlo, degree_high))
        rows.extend(finite_triangle_rows(data, mlo, degree_high,
                                         settings.get("parity_finite_grid", 100)))
        if settings.get("parity_degree_low"):
            rows.extend(finite_root_union_rows(data, settings["parity_degree_low"], degree_high))
        if settings.get("parity_opposite_neighborhoods"):
            from odd_cycle_capacity_rows import opposite_neighborhood_rows

            rows.extend(opposite_neighborhood_rows(data, depth, degree_high, UNIFORM-mlo))
    else:
        rows.extend(clique_repeat_rows(data, mlo, include_losses=True))
        rows.extend(triangle_signature_rows(data, mlo, stronger=True))
    if settings.get("weighted_cycle_floor"):
        floor_mass = mlo
        if settings.get("parity_fixed_degree"):
            fixed_degree = settings["parity_fixed_degree"]
            floor_mass = F(fixed_degree**2+(fixed_degree//2)**2+1,fixed_degree**2)
            assert mlo <= floor_mass <= mhi
        assert floor_mass >= F(98, 81)
        base, weight = old_cycle_implication()
        # All realized e <= 1-M/2 <= 32/81 in this branch.
        # Round downward; every trial uses a bounded denominator.
        minimum = F(floor(100000*(floor_mass-base)/weight), 100000)
        rows.append(((minimum, norm), (-F(1), csr_matrix(cycle.astype(np.int64)))))
    new_scale = lcm(scale, *(coef.denominator for row in rows for coef, _ in row))
    assert new_scale < 10**16
    mult = new_scale//scale
    rows_int = [sum(int(coef*new_scale)*vec.astype(np.int64) for coef, vec in row)
                for row in rows]
    iq = vstack([iq*mult, *rows_int, csr_matrix(contains_red_k5(data))*new_scale,
                 common_neighbor_rows(data)*new_scale], format="csr")
    if settings.get("parity_tight_samples"):
        iq = vstack([iq, tight_sample_caps(data, new_scale, mhi, cap, ehi*mhi)], format="csr")
    if settings.get("parity_k4_mantel"):
        assert settings.get("parity_k4_free") or settings.get("parity_d9_moments")
        iq = vstack([iq, weighted_mantel_rows(data)*new_scale], format="csr")
    if settings.get("parity_d11_root_cover"):
        assert settings.get("parity_fixed_degree") == 11
        from d9_repeat_root_rows import root_neighborhood_rows

        iq = vstack([iq, root_neighborhood_rows(data, 11, (16,None))*new_scale], format="csr")
    if settings.get("parity_d15_root_cover"):
        assert settings.get("parity_fixed_degree") == 15
        from d9_repeat_root_rows import root_neighborhood_rows

        iq = vstack([iq, root_neighborhood_rows(data, 15, (21,None))*new_scale], format="csr")
    if settings.get("parity_marked_vertex_min"):
        assert settings.get("parity_d9_moments")
        iq = vstack([iq, d9_marked_vertex_floor(data, new_scale,
                                              settings["parity_marked_vertex_min"])], format="csr")
    eq = eq*mult
    triangle_forbidden = None
    if settings.get("parity_d9_triangle_structure"):
        assert settings.get("parity_d9_moments") and settings.get("parity_marked_vertex_min", 0) >= 24
        from d9_marked_triangle_rows import triangle_structure

        equality_tri, triangle_iq, triangle_allow = triangle_structure(
            data, new_scale, settings.get("parity_d9_triangle_spokes", False))
        triangle_forbidden = set(zip(order[~triangle_allow], data["code"][~triangle_allow],
                                     data["mask"][~triangle_allow]))
        eq = vstack([eq, equality_tri], format="csr")
        iq = vstack([iq, triangle_iq], format="csr")
    if settings.get("parity_finite_triangle_profiles"):
        assert settings.get("parity_fixed_degree") == degree_high and 11 <= degree_high <= 19
        assert triangle_forbidden is None
        from finite_triangle_profiles import finite_triangle_rows as profile_rows

        triangle_iq, triangle_forbidden = profile_rows(data, degree_high, new_scale)
        iq = vstack([iq, triangle_iq], format="csr")
    if settings.get("parity_fixed_degree"):
        assert settings["parity_fixed_degree"] == degree_high
        eq = vstack([eq, fixed_finite_sampling(data, new_scale, degree_high,
                                              settings.get("parity_fixed_repeats"))], format="csr")
    d9 = settings.get("parity_d9_moments")
    if d9:
        assert degree_high == 9 and settings.get("multiplicity") in (None, 2)
        import hashlib
        source = HERE.parent/"三小时续研_九度矩"/"d9_finite_moment.py"
        assert hashlib.sha256(source.read_bytes()).hexdigest() == settings["parity_d9_source_sha256"]
        sys.path.insert(0, str(source.parent))
        from d9_finite_moment import finite_root_rows

        equality9, inequality9 = finite_root_rows(data)

        def rescale_rows(matrix):
            matrix = matrix.astype(np.int64).tocsr(copy=True)
            for i in range(matrix.shape[0]):
                start, stop = matrix.indptr[i:i+2]
                row_values = matrix.data[start:stop]
                if row_values.size:
                    largest = max(abs(int(row_values.min())), abs(int(row_values.max())))
                    assert 0 < largest <= new_scale
                    row_values *= new_scale//largest
            return matrix

        eq = vstack([eq, rescale_rows(equality9)], format="csr")
        iq = vstack([iq, rescale_rows(inequality9)], format="csr")
        if settings.get("parity_d9_repeat_roots"):
            from d9_repeat_root_rows import repeated_root_neighborhood_rows

            iq = vstack([iq, rescale_rows(repeated_root_neighborhood_rows(data))], format="csr")
    print(f"alpha={alpha}, support={cap}, M=[{mlo},{mhi}], e=[{elo},{ehi}], scale={new_scale}",
          flush=True)
    system = restrict_zero_coordinates(
        (eq, iq, [gram*mult for gram in grams], sizes, data, tags, new_scale, obj, roots),
        settings,
    )
    if settings.get("parity_k4_free") or d9:
        assert degree_high and 9 <= degree_high <= 23
        eq, iq, grams, sizes, data, tags, scale, obj, roots = system
        keep = ~contains_red_clique(data, 4).astype(bool)
        if d9:
            from d9_finite_moment import impossible_patterns

            keep &= ~impossible_patterns(data, False).astype(bool)
        if triangle_forbidden is not None:
            keep &= np.fromiter((key not in triangle_forbidden for key in
                                zip(data["order"], data["code"], data["mask"])),
                                dtype=bool, count=len(keep))
        assert all(keep[root] for root in roots)
        roots = tuple(int(np.count_nonzero(keep[:root])) for root in roots)
        print(f"Finite forbidden-pattern suppression: {int((~keep).sum())} extra columns", flush=True)
        system = (eq[:, keep], iq[:, keep], [gram[keep] for gram in grams], sizes,
                  {key: values[keep] for key, values in data.items()}, tags[keep], scale,
                  obj[keep], roots)
    return system
