"""Replay exact mass bounds on contiguous repeat-fraction intervals."""
import argparse
from fractions import Fraction as F
import json
from pathlib import Path
import sys

from half_anchor_flag import CACHE, strengthened_system, verify, verify_projection_inputs
from half_anchor_projection import lower_slack, maximum_support, upper_lines


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificates", type=Path, nargs="+")
    parser.add_argument("--vendor", type=Path)
    parser.add_argument("--mass-lower", type=F, required=True)
    parser.add_argument("--mass-upper", type=F, default=F(128492, 100000))
    parser.add_argument("--repeat-upper", type=F, default=F(421, 2000))
    args = parser.parse_args()
    if args.vendor:
        sys.path.insert(0, str(args.vendor))
    alpha = lower_slack(args.mass_lower, coupled=True)
    support, _ = maximum_support(upper_lines(alpha, F(45119, 100000)))
    repeat_lower = 1-support/args.mass_lower
    assert F(5, 4) <= args.mass_lower <= args.mass_upper
    cursor = repeat_lower
    upper = args.mass_lower
    inputs_cache = {}
    records = sorted((F(record["settings"]["e_low"]), path.name, record)
                     for path in args.certificates if (record := json.loads(path.read_bytes())))
    for low, name, cert in records:
        settings = cert["settings"]
        assert F(settings["mass_low"]) <= args.mass_lower
        assert F(settings["mass_high"]) >= args.mass_upper
        high = F(settings["e_high"])
        assert low <= cursor < high, (low, cursor, high, name)
        key = tuple(settings.get(k) for k in ("direct_certificate", "direct_gamma"))
        if key not in inputs_cache:
            inputs_cache[key] = verify_projection_inputs(settings)
        assert cert["projection_inputs"] == inputs_cache[key]
        result = verify(CACHE, cert, strengthened_system(CACHE, settings))
        if cert["mode"] == "bound":
            upper = max(upper, F(result["rational_bound"]))
        else:
            assert result["rigorous_infeasible"]
        cursor = high
        print(json.dumps(dict(certificate=name, e_low=str(low), e_high=str(high), **result)),
              flush=True)
    assert cursor >= args.repeat_upper, (cursor, args.repeat_upper)
    print(json.dumps(dict(anchor_minimum=str(alpha), support_upper=str(support),
                          repeat_lower=str(repeat_lower), closed_upper=str(upper),
                          decimal=float(upper)), indent=2), flush=True)


if __name__ == "__main__":
    main()
