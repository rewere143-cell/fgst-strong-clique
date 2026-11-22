"""Fixed degree-nine induced-pentagon cases with one doubled bundle."""

import argparse
from fractions import Fraction
from itertools import combinations, product
import json
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory


HERE = Path(__file__).resolve().parent
BASE = HERE.parent
sys.path.insert(0, str(BASE))

from check_c5_dual import verify
from d7_parallel_sat import GraphCNF, file_digest
from d7_verify_parallel import unpack
from d8_anchored_sat import add_anchor_swap_cuts
from d8_parallel_sat import bounded_solve, gzip_file


D = 9
M = 98
BUNDLES = 1


class BalancedCountCNF(GraphCNF):
    def count(self, literals, upper_threshold):
        yes = self.truth
        ones = literals.count(yes)
        data = [x for x in literals if abs(x) != yes]
        extent = min(upper_threshold - ones, len(data))

        def tree(start, end):
            if start + 1 == end:
                return (yes, data[start])
            mid = (start + end) // 2
            left, right = tree(start, mid), tree(mid, end)
            limit = min(extent, len(left)+len(right)-2)
            out = (yes, *(self.variable() for _ in range(limit)))
            for i, a in enumerate(left):
                for j in range(min(len(right), limit+1-i)):
                    if i+j > 0:
                        self.clause(-a, -right[j], out[i+j])
                    if i+j < limit:
                        nxt_l = left[i+1] if i+1 < len(left) else -yes
                        nxt_r = right[j+1] if j+1 < len(right) else -yes
                        self.clause(nxt_l, nxt_r, -out[i+j+1])
            return out

        values = tree(0, len(data)) if extent > 0 else (yes,)
        return [yes if i <= ones else values[i-ones] if i-ones < len(values) else -yes
                for i in range(upper_threshold+1)]


def sizes(slack):
    low = (D-sum(slack)) // 2
    return tuple(low + slack[(i+2)%5] + slack[(i+3)%5] for i in range(5))


def rotations(values):
    return [v[i:]+v[:i] for v in (values, values[::-1]) for i in range(5)]


def patterns(total):
    for four in product(range(total+1), repeat=4):
        last = total-sum(four)
        if last >= 0:
            slack = (*four, last)
            if slack == min(rotations(slack)) and min(sizes(slack)) >= 1:
                yield slack


def bounds(slack):
    parts = sizes(slack)
    for i in range(5):
        j = (i+1)%5
        opposite = (i+3)%5
        required = M-(D*D+parts[(i+2)%5]*parts[(i+4)%5]-slack[i]*slack[j])
        yield i, j, opposite, required


def counted_out(slack):
    return any(slack[i]+slack[j] == 0 or D*(slack[i]+slack[j]) < required
               for i, j, _, required in bounds(slack))


def check_slack_cap():
    source = BASE / "三小时续研_五束" / "triangle_free_projection_5_4.json"
    certificate = verify(source, triangle_free=True, max_error=Fraction(1, 500))
    assert certificate["mode"] == "conditional"
    assert Fraction(certificate["anchor_ratio"]) == Fraction(5, 4)
    gamma, epsilon = (Fraction(certificate[key]) for key in ("gamma", "epsilon"))
    deficit = Fraction(5, 4) - Fraction(M-BUNDLES, D*D)
    q_max = Fraction(16, 27) * Fraction(186, 625)
    maximum = 7 if BUNDLES == 1 else 9
    next_slack = Fraction(maximum + 2, D)
    assert gamma*(Fraction(5, 32) - (Fraction(5, 4)-next_slack)*q_max)-epsilon > deficit
    return {"minimum_slack_at_most": maximum, "source_sha256": certificate["candidate_sha256"],
            "gamma": str(gamma), "epsilon": str(epsilon), "projected_deficit": str(deficit)}


def instance(slack):
    total = sum(slack)
    core_sizes = sizes(slack)
    n_core = sum(core_sizes)
    parts = list(range(5))
    for i, size in enumerate(core_sizes):
        parts.extend([i]*(size-1))
    parts.extend([-1] * (total+4*(total//3)))
    n = len(parts)
    vertices = range(n)
    pairs = tuple(combinations(vertices, 2))
    f = BalancedCountCNF()
    yes, no = f.truth, -f.truth
    host, mark, extra = {}, {}, {}
    for u, v in pairs:
        a, b = parts[u], parts[v]
        if a>=0 and b>=0 and (a-b)%5 in (1,4):
            e = yes
            r = yes if u < 5 else f.variable()
            w = f.variable() if slack[a] and slack[b] else no
        elif (u < 5 and b>=0) or (a>=0 and not slack[a]) or (b>=0 and not slack[b]):
            e = r = w = no
        else:
            e, r, w = (f.variable() for _ in range(3))
        host[u, v], mark[u, v], extra[u, v] = e, r, w
        f.clause(-r, e)
        f.clause(-w, r)

    def get(table, u, v):
        return no if u == v else table[min(u, v), max(u, v)]

    add_anchor_swap_cuts(f, parts, n_core, n, lambda u,v:get(host,u,v), lambda u,v:get(mark,u,v))
    active = []
    host_nine = []
    mark_nine = []
    for u in vertices:
        edge = [get(host,u,v) for v in vertices if v!=u]
        labeled = [get(mark,u,v) for v in vertices if v!=u]
        repeats = [get(extra,u,v) for v in vertices if v!=u]
        host_degree = f.count(edge+repeats, D+1)
        mark_degree = f.count(labeled+repeats, D)
        host_nine.append(host_degree[D])
        mark_nine.append(mark_degree[D])
        f.clause(-host_degree[D+1])
        if u < n_core:
            continue
        presence = f.any(labeled)
        active.append(presence)
        for v in vertices:
            f.clause(-get(host,u,v), presence)
        for i in range(5):
            ring = {(i-1)%5, (i+1)%5}
            f.clause(*(-get(mark,u,v) for v in sorted(ring)),
                     *(get(host,u,v) for v in range(5) if v not in ring))

    def require_count(lits, amount):
        thresholds = f.count(lits, amount+1)
        f.clause(thresholds[amount])
        f.clause(-thresholds[amount+1])

    outside_required = 23-n_core
    if outside_required > 0:
        f.clause(f.count(active, outside_required)[outside_required])
    require_count(list(mark.values()), M-BUNDLES)
    require_count(list(extra.values()), BUNDLES)

    possible = [pair for pair in pairs if mark[pair] != no]
    for (u,v), (x,y) in combinations(possible, 2):
        if u not in (x,y) and v not in (x,y):
            f.clause(-mark[u,v], -mark[x,y],
                     *(get(host,a,b) for a in (u,v) for b in (x,y)))
    for u,v,x in combinations(vertices, 3):
        f.clause(-mark[u,v], -mark[u,x], -mark[v,x])
    for u,v in possible:
        neighbors = [f.disjunction(get(host,u,x), get(host,v,x))
                     for x in vertices if x not in (u,v)]
        cap = f.count(neighbors, 13 if extra[u,v] != no else 11)
        f.clause(-mark[u,v], cap[11])
        if extra[u,v] != no:
            f.clause(-extra[u,v], cap[13])
    for u,v in pairs:
        witnesses = [f.conjunction(host_nine[x],
                       f.conjunction(-get(host,u,x),-get(host,v,x)))
                     for x in vertices if x not in (u,v) and host_nine[x]!=no]
        may_dominate = f.conjunction(mark_nine[u], f.conjunction(mark_nine[v],-mark[u,v]))
        f.clause(may_dominate, *witnesses)
    for i,j,opposite,required in bounds(slack):
        if required <= 0:
            continue
        outer = [f.disjunction(get(host,i,v),get(host,j,v)) for v in range(n_core,n)]
        needed = (required+D-1)//D
        f.clause(f.count(outer,needed)[needed])
        remaining = [table[u,v] for table in (mark,extra) for u,v in pairs
                     if parts[u] in (-1,opposite) and parts[v] in (-1,opposite)]
        f.clause(f.count(remaining,required)[required])

    charge = max(Fraction(D,2),total-2*min(slack))
    missing = [-mark[u,v] for u,v in pairs if v<n_core and (parts[u]-parts[v])%5 in (1,4)]
    sigs = [host[u,v] for u,v in pairs if u<5 and v>=n_core]
    budget = (charge-Fraction(D,2))*total + Fraction(13,2)
    cap_missing = f.count(missing, budget//2+1)
    cap_sigs = f.count(sigs,total)
    for misses,value in enumerate(cap_missing):
        needed = total-(budget-2*misses)//charge
        f.clause(-value, cap_sigs[needed] if needed<=total else no)

    # Permutations within a core part or among exterior vertices preserve
    # every prior condition; in a lexicographically maximal labeling these
    # adjacent swaps never improve the selected adjacency rows.
    for u in range(5,n-1):
        v = u+1
        if parts[u] != parts[v]:
            continue
        tied = yes
        for x in vertices:
            if x in (u,v):
                continue
            for table in (mark,extra,host):
                lo,hi = get(table,u,x),get(table,v,x)
                if lo == hi:
                    continue
                f.clause(-tied,lo,-hi)
                equal = f.disjunction(f.conjunction(lo,hi),f.conjunction(-lo,-hi))
                tied = f.conjunction(tied,equal)
    return f


def case_name(slack):
    return "s"+"".join(map(str,slack))


def process(slack, args):
    name = case_name(slack)
    if counted_out(slack):
        return dict(name=name, result="COUNTED_OUT")
    meta = args.out/(name+".json")
    old = json.loads(meta.read_bytes()) if meta.exists() else None
    if args.verify:
        if not old or old["result"]!="VERIFIED_UNSAT":
            return dict(name=name, result="UNRESOLVED")
        with TemporaryDirectory(prefix="d9_anchor_",dir=args.out) as tmp:
            place = Path(tmp)
            cnf,proof,fresh = (place/path for path in ("input.cnf","proof.lrat","new.cnf"))
            instance(slack).dump(fresh)
            assert unpack(args.out/(name+".cnf.gz"),cnf)==old["cnf_sha256"]==file_digest(fresh)
            assert unpack(args.out/(name+".lrat.gz"),proof)==old["lrat_sha256"]
            run = subprocess.run([str(args.checker),cnf.name,proof.name],cwd=place,
                                 capture_output=True,text=True,check=True)
            assert json.loads(run.stdout)==old["replay"]
        return old
    if old and old["result"]=="VERIFIED_UNSAT":
        return old
    cnf,proof,log = (args.out/(name+suffix) for suffix in (".cnf",".lrat",".log"))
    formula = instance(slack)
    formula.dump(cnf)
    code,limit = bounded_solve(args.solver,cnf,proof,log,args.timeout,args.max_proof_mib*1024**2)
    result = dict(name=name,slack=slack,result="SAT" if code==10 else "UNRESOLVED",
                  code=code,limit=limit,variables=formula.variables,clauses=len(formula.clauses))
    if code==20:
        run = subprocess.run([str(args.checker),cnf.name,proof.name],cwd=args.out,
                             capture_output=True,text=True,check=True)
        result.update(result="VERIFIED_UNSAT",replay=json.loads(run.stdout),
                      cnf_sha256=file_digest(cnf),lrat_sha256=file_digest(proof))
        gzip_file(cnf)
        gzip_file(proof)
    elif proof.exists():
        proof.unlink()
    meta.write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
    print(name,result["result"],limit or "",flush=True)
    return result


def main():
    global BUNDLES
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inventory",action="store_true")
    parser.add_argument("--verify",action="store_true")
    parser.add_argument("--solver",type=Path)
    parser.add_argument("--checker",type=Path,default=BASE/"d7_rup_replay.exe")
    parser.add_argument("--out",type=Path)
    parser.add_argument("--bundles",type=int,choices=(1,2),default=1)
    parser.add_argument("--timeout",type=int,default=45)
    parser.add_argument("--max-proof-mib",type=int,default=80)
    parser.add_argument("--select",nargs="+")
    args = parser.parse_args()
    if not __debug__:
        raise RuntimeError("Run with assertions enabled")
    BUNDLES = args.bundles
    totals = (1,3,5,7) if BUNDLES == 1 else (1,3,5,7,9)
    cases = [slack for total in totals for slack in patterns(total)
             if args.select is None or case_name(slack) in args.select]
    if args.inventory:
        for total in totals:
            eligible = [case_name(slack) for slack in cases if sum(slack)==total and not counted_out(slack)]
            print(total,len(eligible),eligible)
        return
    args.out = (args.out or HERE/f"d9_b{BUNDLES}_anchor_proofs").resolve()
    args.checker = args.checker.resolve()
    if not args.verify:
        if not args.solver:
            parser.error("Supply --solver or --verify")
        args.solver = args.solver.resolve()
        args.out.mkdir(parents=True,exist_ok=True)
    cap = check_slack_cap()
    results = [process(slack,args) for slack in cases]
    report = dict(slack_cap=cap,cases=len(cases),results=results,
                  unresolved=[x["name"] for x in results if x["result"] not in ("VERIFIED_UNSAT","COUNTED_OUT")])
    if args.select is None:
        (args.out/("verified.json" if args.verify else "summary.json")).write_text(
            json.dumps(report,indent=2)+"\n",encoding="utf-8")
    print(json.dumps({"slack_cap":cap,"cases":len(cases),"unresolved":report["unresolved"]}),flush=True)


if __name__ == "__main__":
    main()
