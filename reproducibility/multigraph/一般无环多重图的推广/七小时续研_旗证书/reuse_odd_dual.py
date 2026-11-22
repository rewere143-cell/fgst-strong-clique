"""Re-evaluate frozen parity duals in nearby parameter boxes without optimization."""
import argparse
from fractions import Fraction as F
import json
from pathlib import Path
import sys

from odd_flag_experiments import CACHE, SHADOW, install_sparse_guards, shadow_hashes, system_for
from half_anchor_flag import verify_projection_inputs
from multigraph_weighted_maxdeg_exact import verify


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("cases", type=Path, help="Mapping from output stems to settings overrides.")
    parser.add_argument("--vendor", type=Path)
    args = parser.parse_args()
    if args.vendor:
        sys.path.insert(0, str(args.vendor))
    source = json.loads(args.source.read_bytes())
    assert source["shadow_sha256"] == shadow_hashes(SHADOW)
    assert source["projection_inputs"] == verify_projection_inputs(source["settings"])
    guard = install_sparse_guards()
    for stem, overrides in json.loads(args.cases.read_bytes()).items():
        settings = dict(source["settings"], **overrides)
        candidate = dict(source, settings=settings)
        try:
            system = system_for(settings)
            exact = verify(CACHE, candidate, system)
        except (AssertionError, OverflowError) as error:
            print(json.dumps(dict(run=stem, error=str(error))), flush=True)
            continue
        print(json.dumps(dict(run=stem, arithmetic=guard, exact=exact)), flush=True)
        if exact["rigorous_infeasible"] or F(exact["rational_bound"]) < F(settings["mass_low"]):
            candidate["replay_result"] = exact
            Path(stem+".json").write_text(json.dumps(candidate,separators=(",",":"))+"\n",
                                           encoding="utf-8")


if __name__ == "__main__":
    main()
