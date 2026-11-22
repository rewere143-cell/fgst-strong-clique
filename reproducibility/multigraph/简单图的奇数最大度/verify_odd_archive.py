"""Verify the fixed standalone archive of the odd-degree strong-clique theorem."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parent


def check_inputs():
    manifest = json.loads((ROOT / "SHA256.json").read_text(encoding="utf-8"))
    for relative, expected in manifest["files"].items():
        path = (ROOT / relative).resolve()
        if not path.is_relative_to(ROOT) or path.stat().st_size != expected["bytes"]:
            raise RuntimeError("Invalid input path or byte count: " + relative)
        with path.open("rb") as stream:
            digest = hashlib.sha256()
            for block in iter(lambda: stream.read(1024 * 1024), b""):
                digest.update(block)
        if digest.hexdigest() != expected["sha256"]:
            raise RuntimeError("Input digest mismatch: " + relative)
    return len(manifest["files"])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path,required=True)
    parser.add_argument("--cc")
    parser.add_argument("--minimal-windows-crt",action="store_true")
    args = parser.parse_args()
    if not __debug__:
        raise RuntimeError("Run without -O or -OO")
    files = check_inputs()
    print(json.dumps({"input_hashes_verified": files}),flush=True)
    output = args.output.resolve()
    output.mkdir(parents=True,exist_ok=False)
    environment = os.environ.copy()
    environment["PYTHONOPTIMIZE"] = "0"
    environment["PYTHONUTF8"] = "1"
    source = ROOT / "source_snapshot/reproducibility/run_all.py"
    source_args = ["--output",str(output/"source")]
    if args.cc:
        source_args.extend(("--cc",args.cc))
    if args.minimal_windows_crt:
        source_args.append("--minimal-windows-crt")
    steps = ((source,source_args,"source"),
             (ROOT/"verify_local_defect.py",[],"local_defect"),
             (ROOT/"verify_odd_simple.py",[],"odd_degrees"))
    for script,extra,name in steps:
        log = output / (name+".log")
        with log.open("wb") as stream:
            run = subprocess.run([sys.executable,"-B",str(script),*extra],cwd=ROOT,
                                 env=environment,stdout=stream,stderr=subprocess.STDOUT)
        if run.returncode:
            raise RuntimeError(f"{name} failed; inspect {log}")
        print(json.dumps({"verified":name}),flush=True)
    source_summary = json.loads((output/"source/summary.json").read_text(encoding="utf-8"))
    if not source_summary["all_passed"] or source_summary["exact_bound"]!="5/4":
        raise RuntimeError("The original proof replay did not certify the expected upper bound")
    odd_stop = json.loads((output/"odd_degrees.log").read_text(encoding="utf-8").splitlines()[-1])
    if not odd_stop["finite_arithmetic_passed"]:
        raise RuntimeError("Odd-degree arithmetic replay did not finish")
    summary = dict(all_passed=True,inputs=files,scope="finite simple graphs and every positive odd D",
                   exact_bound="(5*D^2-2*D+1)/4",checks=[name for _,_,name in steps])
    (output/"summary.json").write_text(json.dumps(summary,indent=2)+"\n",encoding="utf-8")
    print(json.dumps(summary),flush=True)


if __name__=="__main__":
    main()
