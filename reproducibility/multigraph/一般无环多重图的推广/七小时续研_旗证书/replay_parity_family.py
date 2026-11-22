"""Replay all verified coefficient certificates for the odd-degree search."""
import argparse
from fractions import Fraction as F
import json
from pathlib import Path
import sys

from odd_flag_experiments import (
    CACHE, SHADOW, install_sparse_guards, shadow_hashes, system_for, verify, verify_projection_inputs,
)
from odd_shadow_model import support_bound


HERE = Path(__file__).resolve().parent
PROOFS = (
    ("d9_alpha1222_structure.json", (9,9)),
    ("d11_alpha818_structure.json", (11,11)),
    ("d13_alpha846_profiles.json", (13,13)),
    ("d15_alpha733_profiles.json", (15,15)),
    ("d17_alpha647_structure.json", (17,17)),
    ("d19_alpha578_structure.json", (19,19)),
    ("odd_17_23_alpha565.json", (21,23)),
    ("odd_25_37_alpha542.json", (25,37)),
    ("odd_39_47_alpha531.json", (39,47)),
    ("odd_49_57_alpha_third.json", (49,57)),
    ("odd_59_alpha228_penalty.json", (59,None)),
)


def threshold(degree):
    return F(degree**2+(degree//2)**2+1, degree**2)


def covered_box(settings, first, last):
    """Check the numerical consequences of the structural premises in the notes."""
    mass = threshold(first)
    assert F(settings["mass_low"]) <= mass
    assert (F(settings["mass_high"]) >= threshold(last) if last is not None
            else F(settings["mass_high"]) >= F(5,4))
    anchor = {9: F(11,9), 11: F(9,11), 13: F(11,13), 15: F(11,15)}.get(first)
    if anchor is None:
        if first >= 49:
            anchor = F(1,3)
        else:
            anchor = min(F(d+(5 if d % 4 == 1 else 3),2*d)
                         for d in range(first,last+1,2))
    assert F(settings["parity_anchor_minimum"]) <= anchor
    assert F(settings["e_low"]) <= 1-support_bound(settings)/mass
    if first == 9:
        repeat_upper = F(17,98)
    elif first >= 59:
        repeat_upper = F(1,4)
    else:
        repeat_upper = 1-mass/2
        if last is not None:
            a = (2-mass-F(1,last**2))/(2+F(1,last))
            assert 0 <= a <= (2-F(1,last))/4
            repeat_upper = min(repeat_upper,(2*a*(1-a)-a/last)/mass)
    assert F(settings["e_high"]) >= repeat_upper


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--vendor", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if not __debug__:
        raise RuntimeError("Run with Python assertions enabled.")
    if args.vendor:
        sys.path.insert(0, str(args.vendor))
    guard = install_sparse_guards()
    known_shadow = shadow_hashes(SHADOW)
    reports = []
    projection_cache = {}
    for filename,(first,last) in PROOFS:
        candidate = json.loads((HERE/filename).read_bytes())
        conditions = candidate["settings"]
        projection_settings = (conditions.get("direct_certificate"), conditions.get("direct_gamma"))
        if projection_settings not in projection_cache:
            projection_cache[projection_settings] = verify_projection_inputs(conditions)
        assert projection_cache[projection_settings] == candidate["projection_inputs"]
        assert known_shadow == candidate["shadow_sha256"]
        covered_box(conditions, first, last)
        result = verify(CACHE, candidate, system_for(conditions))
        assert result == candidate["replay_result"]
        exact = F(result["rational_bound"])
        if result["mode"] == "infeasible":
            assert result["rigorous_infeasible"] and exact < 0
        else:
            assert exact < threshold(first)
        report = dict(certificate=filename, first=first, last=last,
                      minimum_counterexample_mass=str(threshold(first)), checked=result)
        reports.append(report)
        print(json.dumps(report),flush=True)
    if args.output:
        args.output.write_text(json.dumps(dict(certificates=reports, arithmetic=guard),indent=2)+"\n",
                               encoding="utf-8")


if __name__ == "__main__":
    main()
