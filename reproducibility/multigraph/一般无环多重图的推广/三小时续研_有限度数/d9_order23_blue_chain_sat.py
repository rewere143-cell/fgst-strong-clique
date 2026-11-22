"""Exact order-23 triangle-free marked cases with eight to ten blue endpoints."""

import argparse
from concurrent.futures import ThreadPoolExecutor
from itertools import combinations, product
import json
from pathlib import Path
from tempfile import TemporaryDirectory

from d7_parallel_sat import GraphCNF, file_digest
from d7_verify_parallel import unpack
from d8_b9_sat import check_replay, initial_conflict, lex_maximum
from d8_parallel_sat import bounded_solve, gzip_file
from d8_repeat_core_sat import require_at_least, require_exactly


BLUE_SHAPES = {
    "matching": ((0,1),(2,3),(4,5),(6,7)),
    "star": ((0,1),(0,2),(0,3),(4,5),(6,7)),
    "path": ((0,1),(1,2),(2,3),(4,5),(6,7)),
    "twopaths": ((0,1),(1,2),(3,4),(4,5),(6,7)),
    "path9": ((0,1),(1,2),(3,4),(5,6),(7,8)),
    "matching10": ((0,1),(2,3),(4,5),(6,7),(8,9)),
}
EIGHT_SHAPES = ("matching","star","path","twopaths")
POSSIBLE_SIDES = {
    8: ((6,0),(7,0)),
    9: ((5,0),(6,0),(7,0)),
    10: ((4,0),(5,0),(6,0),(4,2),(5,2),(4,3),(5,3)),
}


def formula(a_count, blue_shape, isolates=0):
    f = GraphCNF()
    yes, no = f.truth, -f.truth
    vertices = range(23)
    blue = set(BLUE_SHAPES[blue_shape])
    B = range(1+max(max(e) for e in blue))
    A = range(B.stop,B.stop+a_count)
    C = range(A.stop,23-isolates)
    isolated = range(C.stop,23)
    pairs = tuple(combinations(vertices,2))
    host, mark, double = {}, {}, {}
    possible = []
    for u,v in pairs:
        if (u,v) in blue:
            h, r, d = yes, no, no
        elif u in B:
            h = r = f.variable()
            d = f.variable()
            f.clause(-d,r)
        elif u in A and v in C:
            h = r = yes if u == A.start or v == C.start else f.variable()
            d = no
        else:
            h = r = d = no
        host[u,v], mark[u,v], double[u,v] = h,r,d
        if r != no:
            possible.append((u,v))

    def lit(table, u, v):
        return no if u == v else table[min(u,v),max(u,v)]

    # The unique nontrivial component of U is bipartite and its row
    # neighborhoods are nested. Ordering both sides gives a Ferrers matrix.
    for u,v in product(A,C):
        h = host[u,v]
        if u != A.start:
            f.clause(-h,host[u-1,v])
        if v != C.start:
            f.clause(-h,host[u,v-1])
    require_at_least(f,[mark[u,v] for u,v in product(A,C)],98-9*len(B)+2*len(blue))
    if isolates:
        for v in B:
            a_full = f.count([mark[v,u] for u in A],len(A))[len(A)]
            c_full = f.count([mark[v,u] for u in C],len(C))[len(C)]
            for z in isolated:
                f.clause(-mark[v,z],a_full,c_full)
    require_at_least(f,list(double.values()),1)

    host_full = {}
    mark_full = {}
    repeat2 = {}
    deficits = []
    slack = 11 - 2*len(blue)
    for u in vertices:
        spare = 9 - sum(u in e for e in blue)
        m_inc = [lit(table,u,v) for table in (mark,double) for v in vertices if v!=u]
        d = f.count(m_inc,spare+1)
        mark_full[u] = d[9] if spare == 9 else no
        host_full[u] = d[spare]
        f.clause(-d[spare+1])
        f.clause(d[spare-slack])
        deficits.extend(-t for t in d[1:spare+1])
        j = f.count([lit(double,u,v) for v in vertices if u!=v],3)
        f.clause(-j[3])
        repeat2[u] = j[2]
    require_exactly(f,deficits,slack)
    f.at_most(list(double.values()),18)
    for u,v,w in combinations(vertices,3):
        f.clause(-mark[u,v],-mark[u,w],-mark[v,w])
    for i,uv in enumerate(possible):
        u,v = uv
        for xy in possible[i+1:]:
            if len(set(uv+xy)) == 4:
                f.clause(-mark[uv],-mark[xy],
                         *(lit(host,a,b) for a,b in product(uv,xy)))
        if double[uv] == no:
            continue
        union = [f.disjunction(lit(host,u,x),lit(host,v,x))
                 for x in vertices if x not in uv]
        f.clause(-double[uv],f.count(union,13)[13])
        f.clause(-double[uv],-repeat2[u],-repeat2[v])

    for u,v in pairs:
        undominated = [f.conjunction(host_full[x],f.conjunction(-lit(host,u,x),
                                                               -lit(host,v,x)))
                       for x in vertices if x not in (u,v)]
        f.clause(mark_full[u],*undominated)
        f.clause(mark_full[v],*undominated)
        f.clause(-host[u,v],*undominated)

    # Lexicographic orbit representatives for the prescribed blue graph.
    if blue_shape.startswith("matching"):
        count = len(blue)
        swaps = [((2*i,2*i+1),) for i in range(count)]
        swaps += [((2*i,2*i+2),(2*i+1,2*i+3)) for i in range(count-1)]
    elif blue_shape == "star":
        swaps = [((1,2),),((2,3),),((4,5),),((6,7),),((4,6),(5,7))]
    elif blue_shape == "path":
        swaps = [((0,3),(1,2)),((4,5),),((6,7),),((4,6),(5,7))]
    elif blue_shape == "path9":
        swaps = [((0,2),),((3,4),),((5,6),),((7,8),),
                 ((3,5),(4,6)),((5,7),(6,8))]
    else:
        swaps = [((0,2),),((3,5),),((0,3),(1,4),(2,5)),((6,7),)]
    layout = list(product(B,range(B.stop,23))) + list(combinations(B,2))
    tables = (mark,double)
    word = [lit(table,u,v) for u,v in layout for table in tables]
    for swaps_for_action in swaps:
        permutation = dict(swaps_for_action)
        permutation.update((y,x) for x,y in swaps_for_action)
        rival = [lit(table,permutation.get(u,u),permutation.get(v,v))
                 for u,v in layout for table in tables]
        lex_maximum(f,word,rival)
    return f


def run(args, a, shape, isolates):
    name = f"{shape}_a{a}" + (f"_i{isolates}" if isolates else "")
    cnf, proof, log, status = (args.out / (name+s)
                               for s in (".cnf",".lrat",".log",".json"))
    f = formula(a,shape,isolates)
    if args.verify:
        row = json.loads(status.read_text())
        if row["result"] != "VERIFIED_UNSAT":
            raise ValueError(f"{name} has no verified proof")
        with TemporaryDirectory(dir=args.out) as folder:
            tmp = Path(folder)
            regen, fixed, replay = (tmp/x for x in ("regenerated.cnf","fixed.cnf","fixed.lrat"))
            f.dump(regen)
            if file_digest(regen) != row["cnf_sha256"]:
                raise ValueError("regenerated CNF mismatch")
            if unpack(cnf.with_suffix(".cnf.gz"),fixed) != row["cnf_sha256"]:
                raise ValueError("archived CNF mismatch")
            if unpack(proof.with_suffix(".lrat.gz"),replay) != row["lrat_sha256"]:
                raise ValueError("archived LRAT mismatch")
            if check_replay(tmp,fixed,replay,args.checker) != row["replay"]:
                raise ValueError("replay count mismatch")
    else:
        if status.exists() and json.loads(status.read_text())["result"] == "VERIFIED_UNSAT":
            return json.loads(status.read_text())
        f.dump(cnf)
        hints = initial_conflict(f.clauses)
        if hints:
            proof.write_text(f"{len(f.clauses)+1} 0 " + " ".join(map(str,hints)) + " 0\n")
            log.write_text("The input has a unit contradiction.\n")
            code, limit = 20, None
        else:
            code, limit = bounded_solve(args.solver,cnf,proof,log,args.timeout,args.proof_mib*1024**2)
        row = dict(name=name, variables=f.variables, clauses=len(f.clauses), limit=limit,
                   result="SAT" if code == 10 else "UNKNOWN")
        if code == 20:
            row.update(result="VERIFIED_UNSAT", cnf_sha256=file_digest(cnf),
                       lrat_sha256=file_digest(proof),replay=check_replay(args.out,cnf,proof,args.checker))
            gzip_file(cnf)
            gzip_file(proof)
        elif code != 10 and proof.exists():
            proof.unlink()
        status.write_text(json.dumps(row,indent=2)+"\n")
    print(name,row["result"],row.get("limit") or "",flush=True)
    return row


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--out",type=Path,required=True)
    p.add_argument("--solver",type=Path)
    p.add_argument("--checker",type=Path,
                   default=Path(__file__).resolve().parent.parent / "d7_rup_replay.exe")
    p.add_argument("--verify",action="store_true")
    p.add_argument("--timeout",type=int,default=240)
    p.add_argument("--proof-mib",type=int,default=120)
    p.add_argument("--jobs",type=int,default=1)
    p.add_argument("--shape",nargs="+",choices=tuple(BLUE_SHAPES),default=EIGHT_SHAPES)
    p.add_argument("--side",nargs="+",type=int,choices=(4,5,6,7))
    p.add_argument("--isolates",nargs="+",type=int,choices=(0,2,3))
    args = p.parse_args()
    if not args.verify and not args.solver:
        p.error("provide the proof solver or use --verify")
    args.out = args.out.resolve()
    args.out.mkdir(exist_ok=True,parents=True)
    cases = [(a,shape,i) for shape in args.shape
             for a,i in POSSIBLE_SIDES[1+max(max(e) for e in BLUE_SHAPES[shape])]
             if (args.side is None or a in args.side)
             and (args.isolates is None or i in args.isolates)]
    with ThreadPoolExecutor(args.jobs) as pool:
        results = list(pool.map(lambda item: run(args,*item),cases))
    print(json.dumps({row["name"]:row["result"] for row in results},indent=2))


if __name__ == "__main__":
    main()
