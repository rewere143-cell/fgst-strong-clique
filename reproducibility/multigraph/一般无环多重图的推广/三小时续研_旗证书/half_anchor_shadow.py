"""Replay a targeted sixth-order model using the normalized C5 slack."""
import argparse
from fractions import Fraction as F
import json
from math import ceil, floor, lcm
from pathlib import Path
import sys


HERE = Path(__file__).resolve().parent
BASE = HERE.parent
sys.path.insert(0, str(BASE))

from half_anchor_flag import CACHE, restrict_zero_coordinates, verify_projection_inputs
from half_anchor_projection import (ANCHOR, CONDITIONAL, UNIFORM, lower_slack,
                                    maximum_support, upper_lines)
from multigraph_refit_exact_dual import repair
from multigraph_six_shadow_search import (anchor_six_coefficients, build_shadow,
                                           decorated_anchors, shadow_hashes)
from multigraph_weighted_maxdeg_exact import gap_by_tag, verify


SHADOW = BASE / "multigraph_weighted_maxdeg_6"
STARTING = HERE / "direct_half_refit.json"


def build_system(settings):
    import numpy as np
    from scipy.sparse import csr_matrix, vstack

    # Preserve the existing sixth-order degree equations and the selected
    # projection. Further rows use the stronger anchor inequalities.
    settings = settings.copy()
    mhi = F(settings["mass_high"])
    settings.update(mass_high="128829/100000", simple_support_cap="12333/10000",
                    abundance_gamma="99999/100000", abundance_epsilon="1/500000000",
                    rooted_pentagon=True, anchor_minimum="33/100",
                    anchor_gamma="2841/5000", anchor_epsilon="1/1000000000",
                    anchor_excess=True, shadow_blocks=settings.get("selected_shadow_blocks", []))
    eq, iq, grams, sizes, data, tags, scale, objective, roots = build_shadow(CACHE, SHADOW, settings)
    objective = objective.astype(np.int64)
    mlo = F(settings["mass_low"])
    elo = F(settings["e_low"])
    below_uniform = max(F(0), UNIFORM-mlo)
    assert not below_uniform or settings.get("known_support_and_anchor_bounds") is True
    coupled = bool(settings.get("coupled_slack"))
    alpha = F(1, 2) if below_uniform else lower_slack(mlo, coupled)
    if settings.get("anchor_override"):
        # This is an additional caller-supplied hypothesis on every red C5.
        override = F(settings["anchor_override"])
        assert alpha <= override <= 1 and not below_uniform
        alpha = override
    gamma_direct = F(settings["direct_gamma"]) if settings.get("direct_certificate") else None
    cap, _ = maximum_support(upper_lines(alpha, gamma_direct))
    cap = F(ceil(cap * 100000), 100000)
    o0 = csr_matrix(np.where(tags == 0, objective, 0))
    o1 = csr_matrix(np.where(tags == 1, objective, 0))
    obj = csr_matrix(objective)
    root0 = csr_matrix(np.where((data["order"] == 2) & (tags == 0), 2, 0))
    root1 = csr_matrix(np.where((data["order"] == 2) & (tags == 1), 2, 0))
    norm = root0 + root1
    rows = [
        ((F(1, 2), obj), (-mhi, norm)),
        ((F(1, 2), o0), (F(1, 4), o1), (-cap, norm)),
        ((F(1, 2), o0), (-cap, root0)),
        ((F(1, 4), o1), (-cap, root1)),
    ]
    if settings.get("tree_caps"):
        for k in range(4):
            group = (data["order"] == 6) & (tags == k)
            if group.any():
                rows.append(((F(1), csr_matrix(group.astype(np.int64))),
                             (-gap_by_tag(6, k), root1 if k else root0)))
    depth = int(settings["anchor_tag_depth"])
    plain = (data["order"] == 6) & (tags == 0)
    anchors = {int(code):anchor_six_coefficients(int(code)) for code in data["code"][plain]}
    use, _, good, excess = decorated_anchors(data, plain, anchors, depth)
    assert not np.any((data["order"] == 6) & ~use)
    cycle = (data["order"] == 5) & (data["code"] == 6012)
    g = mlo - UNIFORM
    tangent = alpha
    tangent_slope = F(1) if below_uniform else 1 + 2*g/(tangent*tangent)
    tangent_intercept = (F(1, 2) - 4*below_uniform if below_uniform
                         else F(1, 2) + 4*g/tangent)
    if coupled and not below_uniform:
        left = (alpha*(alpha-F(1, 2))*(1+alpha) - 2*g*(2+alpha))/(1+alpha*alpha)
        right = F(1, 2)-2*g
        tangent_slope = (right-left)/(1-alpha)
        tangent_intercept = tangent_slope*alpha-left
        assert tangent_slope >= F(1, 2)
        assert F(11, 8)*(F(3, 2)+2*g) >= 2*(F(1, 2)+4*g)
    tangent_slope = F(ceil(tangent_slope * 100000), 100000)
    tangent_intercept = F(floor(tangent_intercept * 100000), 100000)
    for k in range(depth + 1):
        cycle_k = csr_matrix(np.where(cycle & (tags == k), 10, 0))
        loss_k = 5 * cycle_k - csr_matrix(good[k])
        extra_k = csr_matrix(excess[k])
        rows.extend((
            ((alpha, cycle_k), (-F(1), loss_k)),
            ((F(1), extra_k), (tangent_intercept, cycle_k), (-tangent_slope, loss_k)),
        ))
        if k:
            continue
        _, gamma_a, eps_a = ANCHOR
        _, gamma_k, eps_k, theta = CONDITIONAL
        rows.append(((F(1, 2), o0), (gamma_a, loss_k), (-UNIFORM-eps_a, root0)))
        rows.append(((F(1, 2), o0), (gamma_k, loss_k), (-theta*gamma_k, cycle_k),
                     (-UNIFORM+theta*gamma_k/8-eps_k, root0)))
        if gamma_direct:
            rows.append(((F(1, 2), o0), (gamma_direct, loss_k), (-gamma_direct/2, cycle_k),
                         (-UNIFORM+gamma_direct/16-F(2, 10**9), root0)))
    if settings.get("red_clique_caps"):
        from k5_turan_rows import clique_repeat_rows

        rows.extend(clique_repeat_rows(data, mlo, bool(settings.get("red_clique_losses"))))
    if settings.get("triangle_signatures"):
        from k5_turan_rows import triangle_signature_rows

        rows.extend(triangle_signature_rows(data, mlo, bool(settings.get("triangle_signatures_v2"))))
    if settings.get("k4_floor"):
        from k5_turan_rows import k4_neighbor_floor

        rows.append(k4_neighbor_floor(data, mlo))
    new_scale = lcm(scale, *(coeff.denominator for row in rows for coeff, _ in row))
    assert new_scale < 10**16, new_scale
    mult = new_scale // scale
    extra_integer = []
    if settings.get("triangle_density_objective"):
        from k5_turan_rows import contains_red_clique

        assert settings.get("triangle_free_marks") and not settings.get("drop_zero_coordinates")
        final_objective = -2 * contains_red_clique(data, 3)
    else:
        final_objective = objective
    if settings.get("triangle_free_marks") and not settings.get("triangle_density_objective"):
        from k5_turan_rows import contains_red_clique

        extra_integer.append(csr_matrix(contains_red_clique(data, 3)) * new_scale)
    if settings.get("k5_free"):
        from k5_turan_rows import contains_red_k5

        extra_integer.append(csr_matrix(contains_red_k5(data)) * new_scale)
    if settings.get("k5_turan"):
        from k5_turan_rows import common_neighbor_rows

        assert settings.get("k5_free")
        extra_integer.append(common_neighbor_rows(data) * new_scale)
    iq = vstack([iq * mult,
                 *(sum(int(coeff * new_scale) * vec for coeff, vec in row) for row in rows),
                 *extra_integer],
                format="csr")
    print(json.dumps({"mass_lower": str(mlo), "minimum_slack": str(alpha),
                      "support_upper_rounded": str(cap), "e_low": str(elo),
                      "equalities": eq.shape[0], "inequalities": iq.shape[0],
                      "coordinates": objective.size, "psd_blocks": len(sizes),
                      "scale": new_scale}), flush=True)
    system = (eq*mult, iq, [matrix*mult for matrix in grams], sizes,
              data, tags, new_scale, final_objective, roots)
    return restrict_zero_coordinates(system, settings)


def run():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("--start", type=Path, default=STARTING)
    parser.add_argument("--vendor", type=Path)
    parser.add_argument("--replay", action="store_true")
    parser.add_argument("--depth", type=int, default=1, choices=(0, 1, 2))
    parser.add_argument("--mass-low", type=F)
    parser.add_argument("--mass-high", type=F)
    parser.add_argument("--e-low", type=F)
    parser.add_argument("--e-high", type=F)
    parser.add_argument("--seconds", type=int, default=300)
    parser.add_argument("--k5-free", action="store_true")
    parser.add_argument("--k5-turan", action="store_true")
    parser.add_argument("--red-clique-caps", action="store_true")
    parser.add_argument("--red-clique-losses", action="store_true")
    parser.add_argument("--triangle-free-marks", action="store_true")
    args = parser.parse_args()
    if args.vendor:
        sys.path.insert(0, str(args.vendor))
    if args.replay:
        cert = json.loads(args.certificate.read_bytes())
        settings = cert["settings"]
        assert cert["shadow_sha256"] == shadow_hashes(SHADOW)
        assert cert["projection_inputs"] == verify_projection_inputs(settings)
        print(json.dumps(verify(CACHE, cert, build_system(settings)), indent=2))
        return
    cert = json.loads(args.start.read_bytes())
    settings = cert["settings"].copy()
    if args.k5_free or args.k5_turan:
        settings["k5_free"] = True
    if args.k5_turan:
        settings["k5_turan"] = True
    if args.red_clique_caps or args.red_clique_losses:
        settings["red_clique_caps"] = True
    if args.red_clique_losses:
        settings["red_clique_losses"] = True
    if args.triangle_free_marks:
        settings["triangle_free_marks"] = True
    settings["anchor_tag_depth"] = args.depth
    for key in ("mass_low", "mass_high", "e_low", "e_high"):
        value = getattr(args, key)
        if value is not None:
            settings[key] = str(value)
    inputs = verify_projection_inputs(settings)
    system = build_system(settings)
    cert["settings"] = settings
    cert["projection_inputs"] = inputs
    cert["shadow_sha256"] = shadow_hashes(SHADOW)
    improved = repair(CACHE, cert, args.seconds, system)
    print(json.dumps(improved["replay_result"], indent=2))
    args.certificate.write_text(json.dumps(improved, separators=(",", ":"))+"\n", encoding="utf-8")


if __name__ == "__main__":
    run()
