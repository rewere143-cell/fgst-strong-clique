"""Replay descending uniform bounds and check the exact parameter coverage."""
import argparse
from fractions import Fraction as F
import json
from pathlib import Path
import sys

from half_anchor_flag import CACHE, HERE, strengthened_system, verify_projection_inputs
from half_anchor_projection import lower_slack, maximum_support, upper_lines
from half_anchor_shadow import SHADOW, build_system, shadow_hashes, verify


DEFAULT_STEPS = (
    "rank6_uniform_1283_exclusion.json",
    "rank6_uniform_1279_exclusion.json",
    "rank6_uniform_1274_exclusion.json",
    "rank6_uniform_1268_exclusion.json",
    "rank6_uniform_sharp_125_exclusion.json",
)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificates", type=Path, nargs="*")
    parser.add_argument("--vendor", type=Path)
    args = parser.parse_args()
    if args.vendor:
        sys.path.insert(0, str(args.vendor))
    starting = json.loads((HERE/"direct_half_scs.json").read_bytes())
    projection = verify_projection_inputs(starting["settings"])
    assert starting["projection_inputs"] == projection
    result = verify(CACHE, starting, strengthened_system(CACHE, starting["settings"]))
    bound = F(result["rational_bound"])
    assert bound < F(128492, 100000)
    fixed_shadow = shadow_hashes(SHADOW)
    repeat_upper = F(421, 2000)
    for file in args.certificates or [HERE/name for name in DEFAULT_STEPS]:
        record = json.loads(file.read_bytes())
        settings = record["settings"]
        assert record["shadow_sha256"] == fixed_shadow
        assert record["projection_inputs"] == projection
        assert not settings.get("known_support_and_anchor_bounds")
        assert not settings.get("anchor_override") and not settings.get("blue_forest_zero")
        assert not settings.get("triangle_free_marks") and not settings.get("triangle_density_objective")
        mlo, mhi = (F(settings[key]) for key in ("mass_low", "mass_high"))
        elo, ehi = (F(settings[key]) for key in ("e_low", "e_high"))
        assert F(5, 4) <= mlo <= bound <= mhi and ehi >= repeat_upper
        alpha = lower_slack(mlo, bool(settings.get("coupled_slack")))
        support, _ = maximum_support(upper_lines(alpha, F(settings["direct_gamma"])))
        assert 1-support/mlo >= elo
        replay = verify(CACHE, record, build_system(settings))
        if replay["mode"] == "bound":
            right = F(replay["rational_bound"])
            bound = max(mlo, right)
        else:
            assert replay["rigorous_infeasible"]
            bound = mlo
        print(json.dumps(dict(certificate=file.name, alpha=str(alpha), support_upper=str(support),
                              necessary_repeat=str(1-support/mlo), final_bound=str(bound),
                              **replay)), flush=True)
    print(json.dumps(dict(final_bound=str(bound), decimal=float(bound)), indent=2))


if __name__ == "__main__":
    main()
