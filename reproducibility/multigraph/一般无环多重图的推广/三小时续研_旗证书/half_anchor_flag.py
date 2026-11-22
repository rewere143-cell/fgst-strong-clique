"""Exact fifth-order replay with projection constraints from the anchor slack."""
import argparse
from fractions import Fraction as F
import json
from math import ceil, lcm
from pathlib import Path
import sys


HERE = Path(__file__).resolve().parent
BASE = HERE.parent
sys.path.insert(0, str(BASE))

from half_anchor_projection import (ABUNDANCE, ANCHOR, CONDITIONAL, UNIFORM,
                                    lower_slack, maximum_support, replay_input,
                                    upper_lines)
from multigraph_refit_exact_dual import repair
from multigraph_weighted_maxdeg_exact import (build_integer, rounded_certificate,
                                             verify)


CACHE = BASE / "multigraph_weighted_maxdeg_5"
STARTING = BASE / "multigraph_maxdeg5_support_near_best_certificate.json"


def restrict_zero_coordinates(system, settings):
    if not settings.get("drop_zero_coordinates"):
        return system
    import numpy as np

    from k5_turan_rows import contains_red_clique, forest_extendable_blue

    eq, iq, grams, sizes, data, tags, scale, objective, roots = system
    drop = np.zeros(len(tags), dtype=bool)
    if settings.get("triangle_free_marks"):
        drop |= contains_red_clique(data, 3).astype(bool)
    elif settings.get("k5_free"):
        drop |= contains_red_clique(data, 5).astype(bool)
    if settings.get("blue_forest_zero"):
        drop |= forest_extendable_blue(data)
    keep = ~drop
    assert not any(drop[i] for i in roots)
    new_roots = tuple(int(np.count_nonzero(keep[:i])) for i in roots)
    reduced = {k: data[k][keep] for k in ("order", "code", "mask", "aut_count",
                                          "normalizer", "twice_obj")}
    print(json.dumps({"excluded_zero_columns": int(drop.sum()),
                      "remaining": int(keep.sum())}), flush=True)
    return (eq[:, keep], iq[:, keep], [g[keep] for g in grams], sizes,
            reduced, tags[keep], scale, objective[keep], new_roots)


def verify_projection_inputs(settings):
    result = [
        replay_input(ABUNDANCE[0], "abundance", *ABUNDANCE[1:]),
        replay_input(ANCHOR[0], "anchor", *ANCHOR[1:]),
        replay_input(CONDITIONAL[0], "conditional", *CONDITIONAL[1:]),
    ]
    if settings.get("direct_certificate"):
        direct = HERE / settings["direct_certificate"]
        assert direct.resolve().parent == HERE
        result.append(replay_input(direct, "conditional", F(settings["direct_gamma"]),
                                   F(2, 10**9), F(1, 2)))
    return result


def strengthened_system(cache, settings):
    import numpy as np
    from scipy.sparse import coo_matrix, csr_matrix, load_npz, vstack

    orientation = settings.get("orientation_full")
    base_settings = dict(settings)
    base_settings.pop("orientation_full", None)
    eq, inequality, grams, sizes, data, tags, original_scale, obj, roots = build_integer(cache, base_settings)
    mlo = F(settings["mass_low"])
    alpha = lower_slack(mlo, bool(settings.get("coupled_slack")))
    gamma = F(settings["direct_gamma"]) if settings.get("direct_certificate") else None
    lines = upper_lines(alpha, gamma)
    support, _ = maximum_support(lines)
    # Keep the common scale small; round the exact upper cap outwards.
    cap = F(ceil(support * 100000), 100000)
    assert cap >= support

    root0 = csr_matrix(np.where((data["order"] == 2) & (tags == 0), 2, 0))
    root1 = csr_matrix(np.where((data["order"] == 2) & (tags == 1), 2, 0))
    norm = root0 + root1
    o0, o1 = [csr_matrix(np.where(tags == k, obj, 0)) for k in (0, 1)]
    cycles = (data["order"] == 5) & (data["code"] == 6012) & (tags == 0)
    assert cycles.sum() == 1 and data["aut_count"][cycles][0] == 10
    q_c = csr_matrix(np.where(cycles, 10, 0))

    sample_parents = np.load(cache.with_suffix(".sample_meta.npz"))["extension_parents"]
    sample = load_npz(cache.with_suffix(".sample.npz")).astype(np.int64)
    sample_tagged = load_npz(cache.with_suffix(".sample_tagged.npz")).astype(np.int64)
    sample_parent_weights = coo_matrix(
        (data["aut_count"][sample_parents], (np.arange(len(sample_parents)), sample_parents)),
        shape=sample.shape, dtype=np.int64,
    ).tocsr()

    rows = [
        ((F(1, 2), o0), (F(1, 4), o1), (-cap, norm)),
        ((F(1, 2), o0), (-cap, root0)),
        ((F(1, 4), o1), (-cap, root1)),
        ((F(1), sample - sample_tagged), (-2 * cap, sample_parent_weights)),
    ]
    rows.extend(((F(1, 2), o0), (beta, q_c), (-bound, root0)) for bound, beta in lines if beta)
    if settings.get("red_clique_caps"):
        from k5_turan_rows import clique_repeat_rows

        rows.extend(clique_repeat_rows(data, mlo, bool(settings.get("red_clique_losses"))))
    if settings.get("triangle_signatures"):
        from k5_turan_rows import triangle_signature_rows

        rows.extend(triangle_signature_rows(data, mlo, bool(settings.get("triangle_signatures_v2"))))
    scale = lcm(original_scale, *(coefficient.denominator for row in rows for coefficient, _ in row))
    assert scale < 10**16, scale
    multiplier = scale // original_scale
    extra_integer = []
    if settings.get("triangle_free_marks"):
        from k5_turan_rows import contains_red_clique

        extra_integer.append(csr_matrix(contains_red_clique(data, 3)) * scale)
    if settings.get("k5_free"):
        from k5_turan_rows import contains_red_k5

        extra_integer.append(csr_matrix(contains_red_k5(data)) * scale)
    if settings.get("k5_turan"):
        from k5_turan_rows import common_neighbor_rows

        assert settings.get("k5_free")
        extra_integer.append(common_neighbor_rows(data) * scale)
    inequalities = vstack([
        inequality * multiplier,
        *(sum(int(coefficient * scale) * matrix for coefficient, matrix in row) for row in rows),
        *extra_integer,
    ], format="csr")
    print(json.dumps({"mass_lower": str(mlo), "minimum_slack": str(alpha),
                      "support_upper_rounded": str(cap), "scale": scale,
                      "equalities": eq.shape[0], "inequalities": inequalities.shape[0],
                      "coordinates": obj.size, "psd_blocks": len(grams)}), flush=True)
    system = (eq * multiplier, inequalities, [gram * multiplier for gram in grams],
              sizes, data, tags, scale, obj, roots)
    if orientation:
        from multigraph_full_orientation import extend_integer

        assert not settings.get("drop_zero_coordinates")
        return extend_integer(cache.parent / orientation, settings, system)
    return restrict_zero_coordinates(system, settings)


def run():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("--vendor", type=Path)
    parser.add_argument("--replay", action="store_true")
    parser.add_argument("--start", type=Path, default=STARTING)
    parser.add_argument("--direct-certificate")
    parser.add_argument("--direct-gamma", type=F)
    parser.add_argument("--mass-low", type=F)
    parser.add_argument("--mass-high", type=F)
    parser.add_argument("--e-low", type=F)
    parser.add_argument("--e-high", type=F)
    parser.add_argument("--seconds", type=int, default=240)
    parser.add_argument("--iterations", type=int, default=6000)
    parser.add_argument("--numerical", type=Path)
    parser.add_argument("--solve", action="store_true")
    parser.add_argument("--inequalities-only", action="store_true")
    parser.add_argument("--k5-free", action="store_true")
    parser.add_argument("--k5-turan", action="store_true")
    parser.add_argument("--red-clique-caps", action="store_true")
    parser.add_argument("--red-clique-losses", action="store_true")
    parser.add_argument("--triangle-free-marks", action="store_true")
    parser.add_argument("--coupled-slack", action="store_true")
    args = parser.parse_args()
    if args.vendor:
        sys.path.insert(0, str(args.vendor))

    if args.replay:
        certificate = json.loads(args.certificate.read_bytes())
        settings = certificate["settings"]
        exact_inputs = verify_projection_inputs(settings)
        assert certificate["projection_inputs"] == exact_inputs
        result = verify(CACHE, certificate, strengthened_system(CACHE, settings))
    else:
        start = json.loads(args.start.read_bytes())
        settings = start["settings"].copy()
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
        if args.coupled_slack:
            settings["coupled_slack"] = True
        if args.direct_certificate:
            assert args.direct_gamma is not None and args.direct_gamma > 0
            settings.update(direct_certificate=args.direct_certificate, direct_gamma=str(args.direct_gamma))
        for key in ("mass_low", "mass_high", "e_low", "e_high"):
            value = getattr(args, key)
            if value is not None:
                settings[key] = str(value)
        exact_inputs = verify_projection_inputs(settings)
        system = strengthened_system(CACHE, settings)
        if args.inequalities_only:
            start["gram_squared_vectors"] = [[] for _ in system[3]]
        if args.solve:
            from multigraph_low_repeat_search import solve

            assert args.numerical is not None
            solve(system, args.seconds, args.iterations, args.numerical)
        if args.numerical:
            certificate = rounded_certificate(CACHE, args.numerical, "bound", settings, system)
        else:
            assert not args.solve
            start["settings"] = settings
            certificate = start
        certificate = repair(CACHE, certificate, args.seconds, system)
        certificate["projection_inputs"] = exact_inputs
        result = certificate["replay_result"]
        args.certificate.write_text(json.dumps(certificate, separators=(",", ":"))+"\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    run()
