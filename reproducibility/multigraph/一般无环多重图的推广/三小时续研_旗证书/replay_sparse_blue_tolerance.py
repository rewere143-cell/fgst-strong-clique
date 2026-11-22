"""Verify a finite tolerance for the suppressed blue columns of a Farkas dual."""
import argparse
from fractions import Fraction as F
import json
from math import lcm
from pathlib import Path
import sys

from half_anchor_shadow import (CACHE, HERE, SHADOW, build_system, shadow_hashes,
                                verify, verify_projection_inputs)
from k5_turan_rows import contains_red_k5, forest_extendable_blue
from replay_odd_triangle_continuity import dual_tolerance


def suppressed_blue_cost(certificate, system):
    equality, inequality, grams, sizes, data, tags, scale, _, _ = system
    ld, vd = certificate["linear_denominator"], certificate["vector_denominator"]
    common = lcm(ld, vd*vd)
    residual = [0] * len(tags)

    def accumulate(rows, multipliers, factor):
        rows = rows.tocsr()
        assert rows.shape[0] == len(multipliers)
        for i, weight in enumerate(multipliers):
            if weight:
                at, end = rows.indptr[i:i+2]
                for j, coefficient in zip(rows.indices[at:end], rows.data[at:end]):
                    residual[j] += weight*factor*int(coefficient)

    accumulate(equality, certificate["equalities"], common//ld)
    accumulate(inequality, certificate["inequalities"], common//ld)
    for g, size, factors in zip(grams, sizes, certificate["gram_squared_vectors"]):
        outer = [0] * size**2
        for vector in factors:
            for i, x in enumerate(vector):
                for j, y in enumerate(vector):
                    outer[i*size+j] += x*y
        accumulate(g.T, outer, -(common//(vd*vd)))

    suppressed = forest_extendable_blue(data) & ~contains_red_k5(data).astype(bool)
    cost = sum(F(-r, int(aut)) for r, aut, dropped in zip(residual, data["aut_count"], suppressed)
               if dropped and r < 0)/(common*scale)
    return cost, int(suppressed.sum())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certificate", type=Path, default=HERE/"sparse_blue_half_farkas.json")
    parser.add_argument("--vendor", type=Path)
    parser.add_argument("--deficit", type=F, default=F(1, 10**12))
    args = parser.parse_args()
    if args.vendor:
        sys.path.insert(0, str(args.vendor))
    certificate = json.loads(args.certificate.read_bytes())
    settings = certificate["settings"]
    assert certificate["mode"] == "infeasible" and settings["blue_forest_zero"]
    assert settings["k5_free"] and settings["drop_zero_coordinates"]
    assert F(settings["e_low"]) == F(9, 400) and F(settings["e_high"]) == F(421, 2000)
    assert F(settings["mass_low"]) == F(5, 4) and F(settings["mass_high"]) == F(1279, 1000)
    assert F(settings["anchor_override"]) == F(1, 2)
    assert not settings.get("k4_floor") and not settings.get("triangle_signatures")
    assert certificate["shadow_sha256"] == shadow_hashes(SHADOW)
    assert certificate["projection_inputs"] == verify_projection_inputs(settings)
    result = verify(CACHE, certificate, build_system(settings))
    assert result["rigorous_infeasible"]
    full = build_system(dict(settings, drop_zero_coordinates=False))
    cost, count = suppressed_blue_cost(certificate, full)
    blue = 16*args.deficit*cost
    mass = dual_tolerance(certificate)
    right = F(result["rational_bound"]) + blue + mass
    assert right < 0
    maximum_tolerated = -(F(result["rational_bound"])+mass)/(16*cost) if cost else None
    print(json.dumps(dict(original=result["rational_bound"], mass_error=str(mass), blue_columns=count,
                          blue_coefficient=str(cost), blue_error=str(blue),
                          maximum_tolerated_fraction=str(maximum_tolerated),
                          approximate_maximum=float(maximum_tolerated) if cost else None,
                          final_right=str(right)), indent=2), flush=True)


if __name__ == "__main__":
    main()
