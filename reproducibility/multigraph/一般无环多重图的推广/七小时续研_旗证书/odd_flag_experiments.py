"""Refit and replay exact flag duals in an odd-degree counterexample box."""
import argparse
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import sys


HERE = Path(__file__).resolve().parent
PREVIOUS = HERE.parent / "三小时续研_旗证书"
sys.path.insert(0, str(PREVIOUS))

from half_anchor_flag import CACHE, verify_projection_inputs
from half_anchor_projection import maximum_support, upper_lines
from half_anchor_shadow import SHADOW, build_system, shadow_hashes, verify
from rank_cut_search import search
from odd_shadow_model import build_odd_system, support_bound
from audit_shadow_scale import install_sparse_guards
from soft_rank_search import soft_search


ORIGINAL = PREVIOUS / "rank6_uniform_sharp_125_exclusion.json"


def settings_from(args, original):
    settings = dict(original["settings"])
    for key in ("parity_anchor_minimum", "parity_support_cap", "parity_degree_high", "parity_finite_grid",
                "parity_k4_free", "weighted_cycle_floor", "multiplicity",
                "triangle_free_marks", "triangle_density_objective", "anchor_override",
                "blue_forest_zero", "parity_fixed_degree", "parity_fixed_repeats",
                "parity_d9_moments", "parity_d9_source_sha256", "parity_assumed_e_lower",
                "parity_tight_samples", "parity_marked_vertex_min", "parity_degree_low",
                "parity_k4_mantel", "parity_d9_triangle_structure", "parity_d9_repeat_roots",
                "parity_opposite_neighborhoods", "parity_d9_triangle_spokes",
                "parity_finite_triangle_profiles", "parity_d11_root_cover",
                "parity_d15_root_cover"):
        settings.pop(key, None)
    settings.update(
        mass_low=str(args.mass_low),
        mass_high=str(args.mass_high),
        e_high=str(args.e_high),
        known_support_and_anchor_bounds=True,
    )
    if args.anchor_minimum is not None:
        settings["parity_anchor_minimum"] = str(args.anchor_minimum)
    if args.support_cap is not None:
        assert args.anchor_minimum is not None
        settings["parity_support_cap"] = str(args.support_cap)
    if args.degree_high is not None:
        assert args.anchor_minimum is not None
        settings["parity_degree_high"] = args.degree_high
        if args.finite_grid is not None:
            settings["parity_finite_grid"] = args.finite_grid
        if args.degree_low:
            settings["parity_degree_low"] = args.degree_low
    if args.k4_free:
        assert args.degree_high is not None
        settings["parity_k4_free"] = True
    if args.multiplicity is not None:
        settings["multiplicity"] = args.multiplicity
    if args.fixed_degree:
        assert args.degree_high == args.fixed_degree
        settings["parity_fixed_degree"] = args.fixed_degree
    if args.fixed_repeats is not None:
        assert args.fixed_degree
        settings["parity_fixed_repeats"] = args.fixed_repeats
    if args.d9_moments:
        assert args.fixed_degree == 9 and args.multiplicity in (None, 2)
        settings["parity_d9_moments"] = True
        source = HERE.parent/"三小时续研_九度矩"/"d9_finite_moment.py"
        settings["parity_d9_source_sha256"] = hashlib.sha256(source.read_bytes()).hexdigest()
        if args.marked_vertex_min:
            settings["parity_marked_vertex_min"] = args.marked_vertex_min
    if args.d9_triangle_structure:
        assert args.d9_moments and args.marked_vertex_min >= 24
        settings["parity_d9_triangle_structure"] = True
    if args.d9_triangle_spokes:
        assert args.d9_triangle_structure
        settings["parity_d9_triangle_spokes"] = True
    if args.d9_repeat_roots:
        assert args.d9_moments
        settings["parity_d9_repeat_roots"] = True
    if args.weighted_cycle_floor:
        assert args.anchor_minimum is not None
        settings["weighted_cycle_floor"] = True
    if args.tight_samples:
        assert args.anchor_minimum is not None
        settings["parity_tight_samples"] = True
    if args.k4_mantel:
        assert args.k4_free or args.d9_moments
        settings["parity_k4_mantel"] = True
    if args.finite_triangle_profiles:
        assert args.k4_free and args.fixed_degree
        settings["parity_finite_triangle_profiles"] = True
    if args.d11_root_cover:
        assert args.fixed_degree == 11
        settings["parity_d11_root_cover"] = True
    if args.d15_root_cover:
        assert args.fixed_degree == 15
        settings["parity_d15_root_cover"] = True
    if args.opposite_neighborhoods:
        assert args.degree_high
        settings["parity_opposite_neighborhoods"] = True
    if args.depth is not None:
        settings["anchor_tag_depth"] = args.depth
    if "parity_anchor_minimum" in settings:
        support = support_bound(settings)
    else:
        support, _ = maximum_support(upper_lines(F(1, 2), F(settings["direct_gamma"])))
        assert support < F(12333, 10000)
    e_min = 1-support/args.mass_low
    if args.e_low > e_min:
        assert args.assume_repeat_lower
        settings["parity_assumed_e_lower"] = True
    settings["e_low"] = str(args.e_low)
    return settings


def system_for(settings):
    if "parity_anchor_minimum" in settings:
        return build_odd_system(settings)
    return build_system(settings)


def run():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--start", type=Path, default=ORIGINAL)
    parser.add_argument("--vendor", type=Path)
    parser.add_argument("--replay", action="store_true")
    parser.add_argument("--check-scale", action="store_true")
    parser.add_argument("--mass-low", type=F)
    parser.add_argument("--mass-high", type=F, default=F(5, 4))
    parser.add_argument("--e-low", type=F)
    parser.add_argument("--assume-repeat-lower", action="store_true",
                        help="Restrict to a chosen repeat interval; the lower end is a premise.")
    parser.add_argument("--e-high", type=F)
    parser.add_argument("--anchor-minimum", type=F)
    parser.add_argument("--support-cap", type=F)
    parser.add_argument("--degree-high", type=int)
    parser.add_argument("--degree-low", type=int)
    parser.add_argument("--fixed-degree", type=int)
    parser.add_argument("--fixed-repeats", type=int)
    parser.add_argument("--d9-moments", action="store_true")
    parser.add_argument("--d9-triangle-structure", action="store_true")
    parser.add_argument("--d9-triangle-spokes", action="store_true")
    parser.add_argument("--d9-repeat-roots", action="store_true")
    parser.add_argument("--marked-vertex-min", type=int)
    parser.add_argument("--finite-grid", type=int, choices=(100, 1000, 2000))
    parser.add_argument("--k4-free", action="store_true")
    parser.add_argument("--k4-mantel", action="store_true")
    parser.add_argument("--finite-triangle-profiles", action="store_true")
    parser.add_argument("--d11-root-cover", action="store_true")
    parser.add_argument("--d15-root-cover", action="store_true")
    parser.add_argument("--opposite-neighborhoods", action="store_true")
    parser.add_argument("--multiplicity", type=int)
    parser.add_argument("--weighted-cycle-floor", action="store_true")
    parser.add_argument("--tight-samples", action="store_true")
    parser.add_argument("--depth", type=int, choices=(1, 2))
    parser.add_argument("--initial-directions", type=Path)
    parser.add_argument("--directions", type=Path)
    parser.add_argument("--cold", action="store_true")
    parser.add_argument("--soft-penalty", type=int)
    parser.add_argument("--soft-no-crossover", action="store_true")
    parser.add_argument("--soft-verbose", action="store_true")
    parser.add_argument("--soft-sdp", action="store_true")
    parser.add_argument("--linear-farkas", action="store_true")
    parser.add_argument("--soft-sdp-direct", action="store_true")
    parser.add_argument("--sdp-refit-seconds", type=int, default=0)
    parser.add_argument("--seconds", type=int, default=3000)
    parser.add_argument("--per-round", type=int, default=900)
    parser.add_argument("--rounds", type=int, default=16)
    parser.add_argument("--cut-limit", type=int, default=24)
    args = parser.parse_args()
    if args.vendor:
        sys.path.insert(0, str(args.vendor))
    if args.replay:
        certificate = json.loads(args.output.read_bytes())
        settings = certificate["settings"]
        assert certificate["projection_inputs"] == verify_projection_inputs(settings)
        assert certificate["shadow_sha256"] == shadow_hashes(SHADOW)
        statistics = install_sparse_guards()
        result = verify(CACHE, certificate, system_for(settings))
        print(json.dumps(dict(arithmetic=statistics, result=result), indent=2), flush=True)
        return

    original = json.loads(args.start.read_bytes())
    assert args.mass_low < F(5, 4)
    settings = settings_from(args, original)
    original["settings"] = settings
    original["projection_inputs"] = verify_projection_inputs(settings)
    original["shadow_sha256"] = shadow_hashes(SHADOW)
    statistics = install_sparse_guards() if args.check_scale else None
    system = system_for(settings)
    if statistics:
        print(json.dumps(dict(arithmetic=statistics)), flush=True)
    if args.linear_farkas:
        from linear_farkas import fit_linear_farkas

        fit_linear_farkas(original, system, args.output, args.seconds, args.soft_verbose)
    elif args.soft_sdp:
        from soft_sdp import soft_sdp

        soft_sdp(original, system, args.output, args.seconds, args.soft_penalty or 500,
                 args.soft_sdp_direct, args.sdp_refit_seconds)
    elif args.soft_penalty:
        soft_search(original, system, args.output, args.seconds, args.rounds, args.cut_limit,
                    args.per_round, args.directions, args.soft_penalty, args.initial_directions,
                    no_crossover=args.soft_no_crossover, verbose=args.soft_verbose)
    else:
        search(original, system, args.output, args.seconds, args.rounds, args.cut_limit, 38,
               args.per_round, not args.cold, args.directions, False, args.initial_directions, 1, 0)


if __name__ == "__main__":
    run()
