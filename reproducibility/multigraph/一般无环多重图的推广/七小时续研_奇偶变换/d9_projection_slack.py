"""Check the projection cap on minimum marked pentagon slack at degree nine."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path
import sys


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path[:0] = [str(ROOT), str(ROOT / "三小时续研_九度矩")]

from check_c5_dual import verify
from d9_anchor_cases import patterns, counted_out, case_name


def cap(bundles, projection_files):
    abundance = verify(ROOT / "c5_abundance_column_candidate_third.json")
    assert abundance["mode"] == "abundance"
    upper_q = F(16, 27) * F(186, 625)
    gap = F(5, 4) - F(98-bundles, 81)
    q_min = max(F(0), F(1, 8) - (gap + F(abundance["epsilon"])) / F(abundance["gamma"]))

    exclusions = []
    for name in projection_files:
        path = Path(name)
        result = verify(path, triangle_free=True, max_error=F(1, 500))
        assert result["mode"] == "conditional"
        rho = F(result["anchor_ratio"])
        gamma = F(result["gamma"])
        error = F(result["epsilon"])
        for next_slack in range(3, 36, 2):
            slope = F(next_slack, 9) - rho
            q = q_min if slope >= 0 else upper_q
            forced_deficit = gamma * (rho/8 + slope*q) - error
            if forced_deficit > gap:
                exclusions.append((next_slack-2, path.name, str(forced_deficit),
                                   result["candidate_sha256"]))
                break

    return min(exclusions) if exclusions else (35, None, None, None)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("bundles", nargs="+", type=int)
    parser.add_argument("--projection", nargs="+", type=Path, default=[
        ROOT / "三小时续研_五束/triangle_free_projection_5_4.json",
        ROOT / "三小时续研_五束/triangle_free_projection_3_2.json",
    ])
    parser.add_argument("--list", action="store_true")
    args = parser.parse_args()
    for b in args.bundles:
        maximum, certificate, forced, digest = cap(b, args.projection)
        cases = [s for total in range(1, maximum+1, 2) for s in patterns(total)]
        # The separately proved odd slack<=3 lemma closes the small anchors.
        remaining = [case_name(s) for s in cases if sum(s)>=5 and not counted_out(s)]
        print(json.dumps({"bundles": b, "slack_cap": maximum, "certificate": certificate,
                          "sha256": digest, "forced_deficit": forced, "shapes": len(cases),
                          "unresolved_shapes": len(remaining),
                          "cases": remaining if args.list else None}), flush=True)


if __name__ == "__main__":
    main()
