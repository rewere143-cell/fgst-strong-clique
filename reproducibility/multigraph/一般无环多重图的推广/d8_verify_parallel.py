"""Regenerate degree-eight rooted formulas and replay their fixed proofs."""

import argparse
from concurrent.futures import ThreadPoolExecutor
import json
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

from d7_parallel_sat import file_digest
from d7_verify_parallel import unpack
from d8_parallel_sat import cases, instance


def verify_case(case, args):
    name = case[0]
    directory = args.proof_dir
    archived_report = json.loads((directory / f"{name}.result.json").read_text())
    if archived_report.get("result") != "VERIFIED_UNSAT":
        raise ValueError(f"{name}: no fixed proof")
    encoding = json.loads((directory / f"{name}.encoding.json").read_text())
    formula, metadata = instance(case, encoding["use_pairs"], encoding["use_local"],
                                 encoding.get("strict_q12", False),
                                 encoding.get("support_order"))
    with TemporaryDirectory(prefix="fgst_d8_", dir=args.scratch) as scratch:
        scratch = Path(scratch)
        generated = scratch / "generated.cnf"
        archived = scratch / "fixed.cnf"
        proof = scratch / "fixed.lrat"
        formula.dump(generated)
        cnf_hash = unpack(directory / f"{name}.cnf.gz", archived)
        lrat_hash = unpack(directory / f"{name}.lrat.gz", proof)
        if cnf_hash != archived_report["cnf_sha256"] or cnf_hash != file_digest(generated):
            raise ValueError(f"{name}: regenerated CNF differs from the archive")
        if lrat_hash != archived_report["lrat_sha256"]:
            raise ValueError(f"{name}: fixed proof digest differs from the archive")
        checked = subprocess.run([str(args.checker), archived.name, proof.name],
                                 cwd=scratch, capture_output=True, text=True, check=True)
    result = json.loads(checked.stdout)
    if result.get("added", 0) <= 0:
        raise ValueError(f"{name}: checker did not record any RUP additions")
    result.update(name=name, q=metadata["q"], p=metadata["p"],
                  w_limit=metadata["w_limit"], strict_q12=encoding.get("strict_q12", False),
                  cnf_sha256=cnf_hash, lrat_sha256=lrat_hash)
    print(name, result["added"], "verified RUP additions", flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("family", choices=("q11", "q12"))
    parser.add_argument("--proof-dir", type=Path)
    parser.add_argument("--scratch", type=Path)
    parser.add_argument("--checker", type=Path)
    parser.add_argument("--report", type=Path)
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--select", nargs="*")
    args = parser.parse_args()
    stage = Path(__file__).resolve().parent
    default_directory = "d8_partial_q11" if args.family == "q11" else "d8_q12_strict"
    args.proof_dir = (args.proof_dir or stage / default_directory).resolve()
    args.scratch = (args.scratch or stage).resolve()
    args.checker = (args.checker or stage / "d7_rup_replay.exe").resolve()
    selected = [case for case in cases() if case[0].startswith(args.family)]
    if args.select:
        selected = [case for case in selected if case[0] in args.select]
    if not selected:
        raise ValueError("no formula selected")
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        rows = list(pool.map(lambda case: verify_case(case, args), selected))
    sources = ("d5_exact_sat.py", "d7_bipartite_ore_coupled.py", "d7_parallel_sat.py",
               "d7_rup_replay.c", "d7_verify_parallel.py", "d8_parallel_sat.py",
               "d8_verify_parallel.py")
    summary = dict(family=args.family, verified=True, cases=len(rows),
                   additions=sum(row["added"] for row in rows), instances=rows,
                   source_sha256={name: file_digest(stage / name) for name in sources})
    if args.report:
        args.report.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(f"Verified {summary['cases']} formulas and {summary['additions']} RUP additions.",
          flush=True)


if __name__ == "__main__":
    main()
