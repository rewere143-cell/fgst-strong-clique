"""Try frozen sixth-order dual multipliers at nearby justified parameter boxes."""
import argparse
from fractions import Fraction as F
import json
from pathlib import Path
import sys

from half_anchor_shadow import CACHE, SHADOW, build_system, shadow_hashes, verify, verify_projection_inputs
from half_anchor_projection import lower_slack, maximum_support, upper_lines


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("prefix")
    parser.add_argument("mass_lowers", type=F, nargs="+")
    parser.add_argument("--vendor", type=Path)
    args = parser.parse_args()
    if args.vendor:
        sys.path.insert(0, str(args.vendor))
    seed = json.loads(args.source.read_bytes())
    assert seed["projection_inputs"] == verify_projection_inputs(seed["settings"])
    assert seed["shadow_sha256"] == shadow_hashes(SHADOW)
    for mlo in args.mass_lowers:
        alpha = lower_slack(mlo, True)
        cap, _ = maximum_support(upper_lines(alpha, F(seed["settings"]["direct_gamma"])))
        if 1-cap/mlo < F(seed["settings"]["e_low"]):
            continue
        for coupled in (False, True):
            settings = dict(seed["settings"], mass_low=str(mlo), coupled_slack=coupled)
            record = dict(seed, settings=settings)
            result = verify(CACHE, record, build_system(settings))
            print(json.dumps(dict(mass_lower=str(mlo), coupled_slack=coupled, **result)), flush=True)
            if F(result["rational_bound"]) < mlo:
                record["replay_result"] = result
                name = f"{args.prefix}_{mlo.numerator}_{mlo.denominator}_{int(coupled)}.json"
                Path(name).write_text(json.dumps(record, separators=(",", ":"))+"\n", encoding="utf-8")


if __name__ == "__main__":
    main()
