"""Verify the complete degree-nine, triangle-free, two-bundle pentagon partition."""

import argparse
from concurrent.futures import ThreadPoolExecutor
import json
from pathlib import Path
import sys
from types import SimpleNamespace


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path[:0] = [str(ROOT), str(ROOT / "三小时续研_九度矩")]

import d9_anchor_cases as anchor


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=int, default=3)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if not __debug__:
        raise RuntimeError("Run with assertions enabled")

    anchor.BUNDLES = 2
    cap = anchor.check_slack_cap()
    old = ROOT / "三小时续研_九度矩/d9_b2_anchor_proofs"
    new = HERE / "d9_b2_baseline"
    old_shapes = {x["name"]: x["result"]
                  for x in json.loads((old/"summary.json").read_bytes())["results"]}
    new_shapes = {x.stem for x in new.glob("s*.json")}
    assert new_shapes == {name for name, state in old_shapes.items() if state == "UNRESOLVED"}
    cases = [s for total in range(1,cap["minimum_slack_at_most"]+1,2) for s in anchor.patterns(total)]
    assert set(old_shapes) == {anchor.case_name(s) for s in cases}
    checker = ROOT / "d7_rup_replay.exe"

    def verify(s):
        name = anchor.case_name(s)
        path = new if name in new_shapes else old
        result = anchor.process(s, SimpleNamespace(out=path, checker=checker, verify=True))
        assert result["result"] in ("COUNTED_OUT", "VERIFIED_UNSAT"), name
        return result

    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        results = list(pool.map(verify, cases))
    checked = [row for row in results if row["result"] == "VERIFIED_UNSAT"]
    report = {"cap": cap, "total": len(results), "proofs": len(checked),
              "counted_out": len(results)-len(checked), "added_rup": sum(r["replay"]["added"] for r in checked),
              "results": results}
    if args.output:
        args.output.write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8")
    print(json.dumps({key: val for key,val in report.items() if key != "results"}, indent=2))


if __name__ == "__main__":
    main()
