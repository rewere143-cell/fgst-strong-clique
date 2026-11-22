"""Replay the simple-projection deficit argument at degree fifteen."""

from fractions import Fraction as F
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0,str(ROOT))

from check_c5_dual import verify


def main():
    if not __debug__:
        raise RuntimeError("Run with assertions enabled")
    abundance = verify(ROOT/"c5_abundance_column_candidate_third.json")
    penalty = verify(ROOT/"c5_conditional_candidate_032_fourth.json")
    assert abundance["mode"] == "abundance"
    assert penalty["mode"] == "conditional"
    theta = F(penalty["anchor_ratio"])
    support_gap = F(penalty["verified_support_gap"])
    gamma = F(penalty["gamma"])
    rows = []
    for extra,slack in ((2,11),(3,13)):
        deficit = F(5,4)-F(275-extra,15**2)
        min_cycles = F(1,8) - (deficit+F(abundance["epsilon"]))/F(abundance["gamma"])
        variable_slack = F(slack,15)-theta
        assert min_cycles > 0 and variable_slack > 0
        forced = support_gap + gamma*variable_slack*min_cycles
        assert forced > deficit
        rows.append(dict(extra=extra,min_slack=slack,deficit=str(deficit),
                         forced_deficit=str(forced),cycle_floor=str(min_cycles)))
    print(json.dumps(dict(rows=rows,abundance_sha256=abundance["candidate_sha256"],
                          penalty_sha256=penalty["candidate_sha256"]),indent=2))


if __name__ == "__main__":
    main()
