"""Re-evaluate frozen triangle and high-repeat duals near the uniform bound."""
import argparse
from fractions import Fraction as F
import json
from pathlib import Path
import sys

from half_anchor_shadow import (BASE, CACHE, HERE, SHADOW, build_system,
                                shadow_hashes, verify, verify_projection_inputs)


def run():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--vendor", type=Path)
    parser.add_argument("--mass-low", type=F, required=True)
    parser.add_argument("--e-low", type=F)
    parser.add_argument("--e-high", type=F)
    parser.add_argument("--high-repeat", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.vendor:
        sys.path.insert(0, str(args.vendor))
    if args.high_repeat:
        names = ["multigraph_maxdeg5_sample_2105_local_refit_certificate.json",
                 "multigraph_maxdeg5_sample_21125_refit_certificate.json",
                 "multigraph_maxdeg5_sample_2125_certificate.json",
                 "multigraph_weighted_maxdeg_refit_upper2155.json",
                 "multigraph_weighted_maxdeg_upper21875.json"]
        assert args.e_low is None and args.e_high is None
        certificates = [BASE / name for name in names]
    else:
        certificates = [HERE / "rank6_triangle_density.json"]
    checked = []
    for path in certificates:
        cert = json.loads(path.read_bytes())
        settings = cert["settings"]
        settings["mass_low"] = str(args.mass_low)
        if args.high_repeat:
            assert not settings.get("counterexample_support_cap")
            result = verify(CACHE, cert)
            target = args.mass_low if cert["mode"] == "bound" else F(0)
        else:
            settings["known_support_and_anchor_bounds"] = True
            for key in ("e_low", "e_high"):
                override = getattr(args, key)
                if override is not None:
                    settings[key] = str(override)
            assert cert["shadow_sha256"] == shadow_hashes(SHADOW)
            assert cert["projection_inputs"] == verify_projection_inputs(settings)
            result = verify(CACHE, cert, build_system(settings))
            target = F(0)
        valid = F(result["rational_bound"]) < target
        print(json.dumps({"source": path.name, "mass_low": str(args.mass_low),
                          "e_low": settings["e_low"], "e_high": settings["e_high"],
                          "valid": valid, **result}), flush=True)
        checked.append({"certificate": cert, "result": result, "valid": valid})
    if args.output and all(record["valid"] for record in checked):
        args.output.write_text(json.dumps(checked, separators=(",", ":")) + "\n",
                               encoding="utf-8")


if __name__ == "__main__":
    run()
