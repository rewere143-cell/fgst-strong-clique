"""Fix a degree-nine repeat forest and build finite proof-logging SAT cases."""

import argparse
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from itertools import combinations
import json
from math import comb
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path[:0] = [str(ROOT), str(ROOT / "三小时续研_九度矩")]

from d9_anchor_cases import BalancedCountCNF
from d7_parallel_sat import file_digest
from d7_verify_parallel import unpack
from d8_parallel_sat import bounded_solve, gzip_file


@dataclass(frozen=True)
class Shape:
    edges: int
    paths: int
    center_edges: int

    @property
    def components(self):
        return self.edges + self.paths

    @property
    def bundles(self):
        return self.edges + 2*self.paths

    @property
    def name(self):
        return f"q{self.edges:02}_{self.paths:02}_{self.center_edges:02}"

    @property
    def baseline(self):
        return 4*comb(self.paths,2)+2*self.edges*self.paths+comb(self.edges,2)

    @property
    def core_budget(self):
        return 14*self.edges+19*self.paths

    @property
    def cut_cap(self):
        return self.core_budget-2*(self.baseline-5*self.paths-self.center_edges)

    @property
    def outside_cap(self):
        cap = self.cut_cap
        c = self.components
        cut_per_vertex = min(c-6,5)
        return cap // cut_per_vertex


def shapes(numbers):
    max_paths = {10:8, 11:7, 12:5, 13:2}
    for bundles in numbers:
        for paths in range(bundles//2 + 1):
            edges = bundles - 2*paths
            c = edges + paths
            if c > 13 or paths > max_paths.get(c, c):
                continue
            if ((bundles == 18) or (bundles == 17 and c >= 11) or
                    (bundles == 16 and c >= 12) or (bundles == 15 and c >= 13)):
                continue
            for center_edges in range(min(comb(paths,2),5*paths//2)+1):
                shape = Shape(edges,paths,center_edges)
                if shape.cut_cap >= (9 if c >= 9 else 0):
                    yield shape


def instance(shape):
    f = BalancedCountCNF()
    yes, no = f.truth, -f.truth
    groups = []
    for size, count in ((3,shape.paths), (2,shape.edges)):
        for _ in range(count):
            at = sum(map(len,groups))
            groups.append(tuple(range(at,at+size)))
    core = sum(map(len,groups))
    n = core + shape.outside_cap
    vertices = range(n)
    pairs = tuple(combinations(vertices,2))
    owner = {u: i for i, group in enumerate(groups) for u in group}
    centers = {groups[i][0] for i in range(shape.paths)}
    host, red = {}, {}
    doubled = set()

    def at(table,u,v):
        return no if u == v else table[min(u,v),max(u,v)]

    def remaining_degree(u):
        return 5 if u in centers else 7 if u < core else 9

    for u,v in pairs:
        own_u, own_v = owner.get(u), owner.get(v)
        if own_u is not None and own_u == own_v:
            e = r = yes if len(groups[own_u])==2 or u in centers else no
            if e == yes:
                doubled.add((u,v))
        else:
            e = f.variable()
            outside = [j for j in range(len(groups)) if j not in (own_u,own_v)]
            allowance = remaining_degree(u)+remaining_degree(v)-2
            r = f.variable() if len(outside) <= allowance else no
            f.clause(-r,e)
        host[u,v], red[u,v] = e,r

    blue = {pair:f.conjunction(host[pair],-red[pair]) for pair in pairs}
    h_full = []
    cut_degrees = {}
    active = []
    for u in vertices:
        neighbors = [at(host,u,v) for v in vertices if v != u]
        wanted = 9-(9-remaining_degree(u))//2
        degree = f.count(neighbors,wanted+1)
        f.clause(-degree[wanted+1])
        h_full.append(degree[wanted])
        if owner.get(u,shape.paths) < shape.paths:
            f.clause(degree[wanted])
        if u >= core:
            present = f.any(at(red,u,v) for v in vertices if v != u)
            active.append(present)
            for e in neighbors:
                f.clause(-e,present)
            cut_degrees[u] = f.count([at(host,u,v) for v in range(core)],9)
            f.clause(-present,cut_degrees[u][shape.components-8])
            for v in range(core):
                need = shape.components-(4 if v in centers else 6)
                f.clause(-at(red,u,v),cut_degrees[u][need])

    if core < 24:
        f.clause(f.count(active,24-core)[24-core])

    cc = [host[u,v] for u,v in pairs if u in centers and v in centers]
    cut = [host[u,v] for u,v in pairs if u < core <= v]
    total_marks = f.count(list(red.values()),99-shape.bundles)
    f.clause(total_marks[98-shape.bundles])
    f.clause(-total_marks[99-shape.bundles])
    center_count = f.count(cc, shape.center_edges+1)
    f.clause(center_count[shape.center_edges])
    f.clause(-center_count[shape.center_edges+1])
    f.at_most(cut,shape.cut_cap)
    if shape.components >= 9:
        f.clause(f.count(cut,9)[9])
    if shape.cut_cap < shape.components:
        for v,w in combinations(range(core,n),2):
            f.clause(-red[v,w])
    else:
        for v,w in combinations(range(core,n),2):
            for d in range(9):
                need = shape.components-d
                f.clause(-red[v,w],cut_degrees[v][d+1],
                         cut_degrees[w][need] if need <= 9 else no)

    if shape.components == 10:
        for x,y in combinations(sorted(centers),2):
            r = red[x,y]
            for z in centers-{x,y}:
                e1,e2 = at(host,x,z),at(host,y,z)
                f.clause(-r,e1,e2)
                f.clause(-r,-e1,-e2)
            for z in vertices:
                foreign_leaf = z < core and owner[z]<shape.paths and owner[z] not in (owner[x],owner[y])
                if (z >= core or foreign_leaf) and z not in centers:
                    f.clause(-r,-at(host,x,z))
                    f.clause(-r,-at(host,y,z))

    # Conditional count of necessary other-path center hits for a red pair.
    for u,v in pairs:
        if red[u,v] in (yes,no):
            continue
        outside = [j for j in range(len(groups)) if j not in (owner.get(u),owner.get(v))]
        allowance = remaining_degree(u)+remaining_degree(v)-2
        need = len(outside)+sum(j<shape.paths for j in outside)-allowance
        if need > 0:
            hits = [at(host,w,groups[j][0]) for w in (u,v) for j in outside if j<shape.paths]
            f.clause(-red[u,v],f.count(hits,need)[need])

    # Every doubled pair has q >= 13 external different neighbors and at
    # least one blue incident spoke.
    for u,v in sorted(doubled):
        neighborhood = [(at(host,u,w),at(host,v,w)) for w in vertices if w not in (u,v)]
        if u in centers:
            # The two endpoint degrees after omitting the doubled pair are
            # six and seven. Thirteen distinct vertices forces disjointness.
            for left,right in neighborhood:
                f.clause(-left,-right)
        else:
            reach = [f.disjunction(left,right) for left,right in neighborhood]
            f.clause(f.count(reach,13)[13])
        f.clause(*(at(blue,w,z) for w in (u,v) for z in vertices if z not in (u,v)))
    for (u,v),(x,y) in combinations([pair for pair in pairs if red[pair]!=no],2):
        if u not in (x,y) and v not in (x,y):
            f.clause(-red[u,v],-red[x,y],*(at(host,a,b) for a in (u,v) for b in (x,y)))

    if core >= 26:
        for u,v,w in combinations(vertices,3):
            f.clause(-red[u,v],-red[u,w],-red[v,w])
        side = [f.variable() for _ in vertices]
        clean = [-f.any(at(blue,u,v) for v in vertices if v!=u) for u in vertices]
        for u,v in pairs:
            f.clause(-red[u,v],-clean[u],-clean[v],side[u],side[v])
            f.clause(-red[u,v],-clean[u],-clean[v],-side[u],-side[v])
    for u,v in pairs:
        f.clause(*(f.conjunction(h_full[w],f.conjunction(-at(host,u,w),-at(host,v,w)))
                   for w in vertices if w not in (u,v) and h_full[w]!=no))

    def maximal_under(swaps):
        perm = dict(swaps)
        perm.update({v:u for u,v in swaps})
        equal = yes
        for u,v in pairs:
            x,y = perm.get(u,u),perm.get(v,v)
            for table in (red,host):
                first,second = table[u,v],at(table,x,y)
                if first == second:
                    continue
                f.clause(-equal,first,-second)
                same = f.disjunction(f.conjunction(first,second),f.conjunction(-first,-second))
                equal = f.conjunction(equal,same)

    for group in groups:
        maximal_under([(group[-2],group[-1])])
    for left,right in zip(groups,groups[1:]):
        if len(left)==len(right):
            maximal_under(list(zip(left,right)))
    for v in range(core,n-1):
        maximal_under([(v,v+1)])
    return f


def task(shape,args):
    name = shape.name
    cnf,cert,log,data = (args.out/f"{name}.{ext}" for ext in ("cnf","lrat","log","json"))
    if data.is_file():
        previous = json.loads(data.read_bytes())
        if previous["result"]=="VERIFIED_UNSAT":
            if args.verify:
                with TemporaryDirectory(prefix="fixed_core_",dir=args.out) as path:
                    path = Path(path)
                    old,new,lrat = (path/text for text in ("old.cnf","new.cnf","old.lrat"))
                    instance(shape).dump(new)
                    assert unpack(cnf.with_suffix(".cnf.gz"),old)==previous["cnf_sha256"]==file_digest(new)
                    assert unpack(cert.with_suffix(".lrat.gz"),lrat)==previous["lrat_sha256"]
                    proc = subprocess.run([str(args.checker),old.name,lrat.name],cwd=path,
                                          capture_output=True,text=True,check=True)
                    assert json.loads(proc.stdout)==previous["replay"]
            print(name,"REPLAY_PASS" if args.verify else "VERIFIED_UNSAT",flush=True)
            return previous
    if args.verify:
        return {"name":name,"result":"UNRESOLVED"}
    f = instance(shape)
    f.dump(cnf)
    code, cap = bounded_solve(args.solver,cnf,cert,log,args.timeout,args.proof_mib*1024**2)
    result = {"name":name,"bundles":shape.bundles,"shape":shape.__dict__,
              "result":"SAT" if code==10 else "UNRESOLVED","limit":cap,"code":code,
              "variables":f.variables,"clauses":len(f.clauses)}
    if code==20:
        proc = subprocess.run([str(args.checker),cnf.name,cert.name],cwd=args.out,
                              capture_output=True,text=True,check=True)
        result.update(result="VERIFIED_UNSAT",cnf_sha256=file_digest(cnf),
                      lrat_sha256=file_digest(cert),replay=json.loads(proc.stdout))
        gzip_file(cnf)
        gzip_file(cert)
    elif cert.is_file():
        cert.unlink()
    data.write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
    print(name,result["result"],cap or "",flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("bundles",nargs="+",type=int)
    parser.add_argument("--select",nargs="+")
    parser.add_argument("--inventory",action="store_true")
    parser.add_argument("--out",type=Path)
    parser.add_argument("--solver",type=Path)
    parser.add_argument("--checker",type=Path,default=ROOT/"d7_rup_replay.exe")
    parser.add_argument("--verify",action="store_true")
    parser.add_argument("--timeout",type=int,default=200)
    parser.add_argument("--proof-mib",type=int,default=250)
    parser.add_argument("--jobs",type=int,default=1)
    args = parser.parse_args()
    if not __debug__:
        raise RuntimeError("Run with assertions enabled")
    assert all(15<=n<=18 for n in args.bundles)
    cases = [shape for shape in shapes(args.bundles) if args.select is None or shape.name in args.select]
    if args.inventory:
        print(json.dumps({s.name:{"bundles":s.bundles,"cut":s.cut_cap,"outside":s.outside_cap} for s in cases}))
        return
    assert args.out is not None
    args.out = args.out.resolve()
    args.checker = args.checker.resolve()
    if not args.verify:
        assert args.solver is not None
        args.solver = args.solver.resolve()
        args.out.mkdir(parents=True,exist_ok=True)
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        records = list(pool.map(lambda s:task(s,args),cases))
    print(json.dumps({"cases":len(records),
                      "unresolved":[r["name"] for r in records if r["result"]!="VERIFIED_UNSAT"]}))


if __name__=="__main__":
    main()
