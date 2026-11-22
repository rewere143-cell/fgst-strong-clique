"""Regenerate all fixed degree-seven parallel-subcase CNFs and replay LRAT."""
from concurrent.futures import ThreadPoolExecutor
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
import argparse
import gzip
import json
import subprocess

from d7_parallel_sat import cases, instance, file_digest


def unpack(source, target):
    digest = sha256()
    with gzip.open(source, "rb") as stream, target.open("wb") as dest:
        for data in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(data)
            dest.write(data)
    return digest.hexdigest()


def verify_case(case, stage, checker, scratch):
    name = case[0]
    directory = stage / ("d7_parallel_sat_cuts_q10" if name.startswith("q10") else
                         "d7_parallel_sat_cuts_q9")
    stored_cnf = directory / (name + ".cnf.gz")
    stored_lrat = directory / (name + ".lrat.gz")
    prior = json.loads((directory / (name + ".result.json")).read_text())
    if prior.get("result") != "VERIFIED_UNSAT":
        raise ValueError(f"{name}: previous run did not produce a fixed proof")
    formula, row = instance(case)
    with TemporaryDirectory(prefix="fgst_parallel_", dir=scratch) as work:
        work = Path(work)
        generated, archived, proof = (work / suffix for suffix in
                                      ("generated.cnf", "fixed.cnf", "fixed.lrat"))
        formula.dump(generated)
        cnf_sha256 = unpack(stored_cnf, archived)
        if (cnf_sha256 != prior["cnf_sha256"] or
                generated.read_bytes() != archived.read_bytes()):
            raise ValueError(f"{name}: regenerated CNF differs from fixed one")
        lrat_sha256 = unpack(stored_lrat, proof)
        if lrat_sha256 != prior["lrat_sha256"]:
            raise ValueError(f"{name}: saved LRAT digest differs")
        replay = subprocess.run([str(checker), archived.name, proof.name],
                                cwd=work, text=True, capture_output=True,
                                check=True)
    result = json.loads(replay.stdout)
    if result.get("added", 0) <= 0:
        raise ValueError(f"{name}: checker output does not report additions")
    result.update(name=name, q=row["q"], p=row["p"], w=row["w"],
                  variables=formula.variables, clauses=len(formula.clauses),
                  cnf_sha256=cnf_sha256, lrat_sha256=lrat_sha256)
    print(name, result["added"], "verified RUP additions", flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--stage", type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument("--checker", type=Path)
    parser.add_argument("--scratch", type=Path)
    parser.add_argument("--report", type=Path)
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--family")
    args = parser.parse_args()
    stage = args.stage.resolve()
    checker = (args.checker or stage / "d7_rup_replay.exe").resolve()
    scratch = (args.scratch or stage).resolve()
    selected = [case for case in cases() if not args.family or case[0].startswith(args.family)]
    if not selected:
        raise ValueError("no cases selected")
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        rows = list(pool.map(lambda case: verify_case(case, stage, checker, scratch), selected))
    source_hashes = {
        name: file_digest(stage / name) for name in (
            "d5_exact_sat.py", "d7_bipartite_ore_coupled.py", "d7_parallel_sat.py",
            "d7_rup_replay.c", "d7_verify_parallel.py"
        )
    }
    results = dict(verified=True, cases=len(rows),
                   additions=sum(row["added"] for row in rows),
                   deleted_clauses=sum(row["deleted"] for row in rows),
                   source_sha256=source_hashes, instances=rows)
    if args.report:
        args.report.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(f"Verified {results['cases']} instances and {results['additions']} RUP additions.",
          flush=True)


if __name__ == "__main__":
    main()

