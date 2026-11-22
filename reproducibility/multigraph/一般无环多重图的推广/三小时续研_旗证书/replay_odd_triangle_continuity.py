"""Use verified duals with an explicit tolerance below normalized mass 5/4."""
from fractions import Fraction as F
import argparse
import json
from pathlib import Path
import sys

from half_anchor_shadow import (BASE, CACHE, HERE, SHADOW, build_system,
                                shadow_hashes, verify, verify_projection_inputs)


UNIFORM = F(5, 4)
DELTA = F(1, 10**36)
PRIOR_FILES = (
    "multigraph_maxdeg5_sample_2105_local_refit_certificate.json",
    "multigraph_maxdeg5_sample_21125_refit_certificate.json",
    "multigraph_maxdeg5_sample_2125_certificate.json",
    "multigraph_weighted_maxdeg_refit_upper2155.json",
    "multigraph_weighted_maxdeg_upper21875.json",
)


def dual_tolerance(certificate):
    # The accompanying proof bounds each row violation and each negative
    # Gram entry error by 10^6 DELTA in this fixed family.
    lden = certificate["linear_denominator"]
    vden = certificate["vector_denominator"]
    linears = F(sum(certificate["inequalities"]), lden)
    grams = F(sum(sum(abs(x) for x in vector)**2
                  for block in certificate["gram_squared_vectors"]
                  for vector in block), vden*vden)
    return 10**6 * DELTA * (linears + grams)


def replay(path, shadow=False, uniform=False):
    certificate = json.loads(path.read_bytes())
    settings = certificate["settings"]
    assert F(settings["mass_low"]) == UNIFORM
    if shadow:
        assert not settings.get("k4_floor") and not settings.get("anchor_override")
        assert not settings.get("blue_forest_zero")
        if uniform:
            assert not settings.get("triangle_free_marks")
            assert not settings.get("triangle_density_objective")
            assert settings.get("triangle_signatures_v2")
        else:
            assert settings["triangle_density_objective"]
        assert certificate["shadow_sha256"] == shadow_hashes(SHADOW)
        assert certificate["projection_inputs"] == verify_projection_inputs(settings)
        result = verify(CACHE, certificate, build_system(settings))
    else:
        assert not settings.get("counterexample_support_cap")
        result = verify(CACHE, certificate)
    corrected = F(result["rational_bound"]) + dual_tolerance(certificate)
    if shadow and not uniform:
        target = -F(7, 500)
    elif result["mode"] == "bound":
        target = UNIFORM - DELTA
    else:
        target = F(0)
    assert corrected < target, (path, corrected, target)
    print(json.dumps(dict(certificate=path.name, original=result["rational_bound"],
                          error=str(dual_tolerance(certificate)), adjusted=str(corrected),
                          decimal=float(corrected), target=str(target))), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--vendor", type=Path)
    parser.add_argument("--uniform", action="store_true",
                        help="Replay the tolerance of the unrestricted uniform sharp dual.")
    args = parser.parse_args()
    if args.vendor:
        sys.path.insert(0, str(args.vendor))
    for name in PRIOR_FILES:
        replay(BASE / name)
    if args.uniform:
        replay(HERE / "rank6_uniform_sharp_125_exclusion.json", shadow=True, uniform=True)
    else:
        replay(HERE / "rank6_triangle_density.json", shadow=True)


if __name__ == "__main__":
    main()
