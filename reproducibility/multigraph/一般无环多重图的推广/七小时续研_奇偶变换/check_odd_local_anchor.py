"""Replay the existing widening argument from a prescribed marked pentagon."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from check_anchored_multigraph_constants import (
    grid_up, old_core, old_core_for_anchor, wider_step,
)


PRIOR_SUPPORT = (
    (323,F(105,10000)), (451,F(115,10000)), (651,F(175,10000)),
    (801,F(18,1000)), (1501,F(1959,100000)), (2501,F(2025,100000)),
)


def close(min_degree, anchor):
    assert min_degree >= 9 and F(0)<anchor<F(1,2)
    mu = F(1,2*min_degree)-F(5,4*min_degree**2)
    earlier = max((tol for d,tol in PRIOR_SUPPORT if d<=min_degree), default=F(0))
    current = F(5,4)
    trace = []
    for index in range(12):
        imposed = F(1)
        choices = []
        for _ in range(12):
            try:
                old = (old_core_for_anchor(anchor,mu,imposed) if index == 0
                       else old_core(current,mu,imposed))
            except AssertionError:
                return {"proved":False,"trace":trace,"reason":"insufficient initial cover"}
            candidates = []
            for mode in ("all","three"):
                try:
                    candidate = wider_step(old,mu,mode)
                except AssertionError:
                    candidate = None
                if candidate is not None:
                    candidates.append(candidate)
            if not candidates:
                return {"proved":False,"trace":trace,"reason":"no positive coefficient"}
            coeff, slack_fee, missing_fee, mode, factor = max(candidates,key=lambda s:s[0])
            reduced = grid_up(mu/coeff)
            choices.append({"mode":mode,"coefficient":str(coeff),"slack_fee":str(slack_fee),
                            "missing_fee":str(missing_fee),"hole_factor":str(factor),
                            "support_deficit":str(reduced)})
            if slack_fee>F(1,3) and factor==1:
                return {"proved":True,"method":"parity of enlarged slack","trace":[*trace,choices]}
            if reduced<=earlier:
                return {"proved":True,"method":"known support tolerance","tolerance":str(earlier),
                        "trace":[*trace,choices]}
            next_imposed = grid_up(mu/missing_fee)
            if next_imposed>=imposed:
                break
            imposed = next_imposed
        trace.append(choices)
        if reduced>=current:
            break
        current = reduced
    return {"proved":False,"trace":trace,"reason":"no improvement"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("degree", type=int, nargs="+")
    parser.add_argument("--anchor", type=F, default=F(1,10))
    parser.add_argument("--require-proof", action="store_true")
    args = parser.parse_args()
    if not __debug__:
        raise RuntimeError("Run with assertions enabled")
    for d in args.degree:
        report = close(d,args.anchor)
        print(json.dumps({"minimum_degree":d,"anchor":str(args.anchor),**report}),flush=True)
        if args.require_proof and not report["proved"]:
            raise SystemExit(f"Could not close D >= {d}")


if __name__ == "__main__":
    main()
