"""Regenerate and replay the 34 fixed D9 / n=23 SAT certificates."""
from concurrent.futures import ThreadPoolExecutor
from itertools import product
from pathlib import Path
from tempfile import TemporaryDirectory
import argparse
import json
import subprocess

import d9_n23_trianglefree_sat as trianglefree
import d9_n23_twin_sat as twins
from d7_parallel_sat import file_digest


def all_cases():
    for p,d in product((2,3),range(1,5)):
        yield "d9_n23_twin_sat",f"p{p}_d{d}",twins.instance,(p,d)
    for name,deficit,side in trianglefree.all_cases():
        yield "d9_n23_trianglefree_sat",name,trianglefree.instance,(deficit,side)


def verify(case, stage, checker):
    subdir,name,generator,parameters=case
    source=stage/subdir
    result=json.loads((source/(name+".json")).read_text())
    if result.get("code")!=20:
        raise ValueError(f"{name}: missing fixed UNSAT proof")
    formula=generator(*parameters)
    original=source/(name+".cnf")
    lrat=source/(name+".lrat")
    with TemporaryDirectory(prefix="d9_n23_") as temp:
        regenerated=Path(temp)/"regenerated.cnf"
        formula.dump(regenerated)
        if regenerated.read_bytes()!=original.read_bytes():
            raise ValueError(f"{name}: regenerated CNF differs")
    if file_digest(original)!=result["cnf_sha256"] or file_digest(lrat)!=result["lrat_sha256"]:
        raise ValueError(f"{name}: observed certificate digest mismatch")
    replay=subprocess.run([str(checker),original.name,lrat.name],cwd=source,
                          check=True,text=True,capture_output=True)
    observed=json.loads(replay.stdout)
    if observed!=result["replay"]:
        raise ValueError(f"{name}: independently replayed clause counts differ")
    result.update(branch=subdir,replay=observed)
    print(name,observed["added"],"verified",flush=True)
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--checker",type=Path)
    parser.add_argument("--report",type=Path)
    parser.add_argument("--jobs",type=int,default=2)
    args=parser.parse_args()
    stage=Path(__file__).resolve().parent
    checker=(args.checker or stage/"d7_rup_replay.exe").resolve()
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        rows=list(pool.map(lambda case:verify(case,stage,checker),all_cases()))
    files=("d9_n23_twin_sat.py","d9_n23_trianglefree_sat.py","d9_verify_n23.py",
           "d9_n23_c5_saturated.py","d9_n23_twin_triangle.py","d7_parallel_sat.py",
           "d7_bipartite_ore_coupled.py","d5_exact_sat.py","d7_rup_replay.c",
           "source_snapshot/reproducibility/verifiers/c_runtime.h")
    summary=dict(verified=True,instances=len(rows),
                 additions=sum(row["replay"]["added"] for row in rows),
                 sources={n:file_digest(stage/n) for n in files},proofs=rows)
    if args.report:
        args.report.write_text(json.dumps(summary,indent=2)+"\n",encoding="utf-8")
    print(f"{summary['instances']} instances, {summary['additions']} RUP additions verified.")


if __name__=="__main__":
    main()

