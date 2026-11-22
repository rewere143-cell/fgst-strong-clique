"""Refit the first-and-extra moment certificate on separate repeat intervals."""
import argparse
from fractions import Fraction as F
import json
from pathlib import Path
import sys

from half_anchor_flag import CACHE, strengthened_system, verify_projection_inputs
from rank_cut_search import search


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("start", type=Path)
    parser.add_argument("prefix")
    parser.add_argument("breakpoints", type=F, nargs="+")
    parser.add_argument("--vendor", type=Path)
    parser.add_argument("--mass-low", type=F, required=True)
    parser.add_argument("--mass-high", type=F, required=True)
    parser.add_argument("--seconds", type=int, default=120)
    parser.add_argument("--triangle-signatures", action="store_true")
    parser.add_argument("--coupled-slack", action="store_true")
    args = parser.parse_args()
    if args.vendor:
        sys.path.insert(0, str(args.vendor))
    initial = json.loads(args.start.read_bytes())
    assert args.breakpoints == sorted(set(args.breakpoints))
    for i, (lo, hi) in enumerate(zip(args.breakpoints, args.breakpoints[1:])):
        settings = dict(initial["settings"], e_low=str(lo), e_high=str(hi),
                        mass_low=str(args.mass_low), mass_high=str(args.mass_high),
                        red_clique_losses=True)
        if args.triangle_signatures:
            settings["triangle_signatures"] = True
        if args.coupled_slack:
            settings["coupled_slack"] = True
        record = dict(initial, settings=settings)
        record["projection_inputs"] = verify_projection_inputs(settings)
        system = strengthened_system(CACHE, settings)
        output = Path(f"{args.prefix}_{i:02}.json")
        print(json.dumps(dict(interval=[str(lo), str(hi)], output=output.name)), flush=True)
        search(record, system, output, args.seconds, 2, 24, 0, args.seconds, False, None,
               False, None, 1, 0)


if __name__ == "__main__":
    main()
