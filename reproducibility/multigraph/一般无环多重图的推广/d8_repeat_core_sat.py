"""Exact degree-eight search rooted on the full matching of doubled bundles."""

import argparse
from concurrent.futures import ThreadPoolExecutor
from contextlib import nullcontext
from functools import cache
import gzip
from itertools import combinations, permutations, product
import json
from pathlib import Path
import shutil
import subprocess
from tempfile import TemporaryDirectory

from d7_parallel_sat import GraphCNF, file_digest
from d7_verify_parallel import unpack
from d8_parallel_sat import bounded_solve, gzip_file


def require_at_least(formula, literals, lower):
    formula.clause(formula.count(literals,lower)[lower])


def require_exactly(formula, literals, number):
    counts = formula.count(literals,number+1)
    formula.clause(counts[number])
    formula.clause(-counts[number+1])


def partitions(total, low, length=None):
    if not total:
        if length in (None, 0):
            yield ()
        return
    if length == 0:
        return
    for first in range(low, total+1):
        for tail in partitions(total-first, first, None if length is None else length-1):
            yield (first,)+tail


EXTERIOR_PROFILES = {
    0: (
        ((8,8,6),(),(),()),
        ((7,7,8),((0,1),),(),()),
        ((7,7,4,4),((0,2),(1,3)),((0,2),(1,3)),((2,3),)),
    ),
    1: (
        ((7,8,5),((0,2),),((0,2),),()),
    ),
}


B10_SMALL_COMPONENTS = (
    (1,()),
    (2,((0,1),)),
    (3,((0,1),(1,2))),
    (3,((0,1),(1,2),(0,2))),
    (4,((0,1),(1,2),(2,3))),
    (4,((0,1),(0,2),(0,3))),
    (4,((0,1),(1,2),(2,3),(0,3))),
    (4,((0,1),(1,2),(0,2),(0,3))),
    (5,((0,1),(1,2),(2,3),(3,4))),
    (5,((0,1),(0,2),(0,3),(3,4))),
)

B10_PROFILES = {
    2: (
        ((6,5,5,5,5),tuple(e for e in combinations(range(5),2)
                           if e not in {(0,1),(0,2),(3,4)}),(),()),
    ),
    3: (
        ((8,8,8),(),(),()),
        ((6,6,6,6),((0,1),(1,2),(2,3),(0,3)),(),()),
    ),
    4: (
        ((7,7,8),((0,1),),(),()),
    ),
}


def graph_orbits(order):
    edges = tuple(combinations(range(order),2))
    slots = {edge:i for i,edge in enumerate(edges)}
    relabelings = tuple(permutations(range(order)))
    moves = [tuple(1<<slots[tuple(sorted((p[u],p[v])))] for u,v in edges)
             for p in relabelings]
    unseen = set(range(1<<len(edges)))
    while unseen:
        representative = min(unseen)
        indices = tuple(i for i in range(len(edges)) if representative>>i&1)
        orbit = [sum(move[i] for i in indices) for move in moves]
        unseen.difference_update(orbit)
        yield representative,tuple(edges[i] for i in indices),[
            p for p,new in zip(relabelings,orbit) if new==representative
        ]


@cache
def ten_outer_shapes(order,slots):
    shapes = []
    for mask,edges,automorphisms in graph_orbits(order):
        neighbors = tuple({v if u==i else u for u,v in edges if i in (u,v)}
                          for i in range(order))
        capacity = tuple(8-len(near) for near in neighbors)
        for hits in product(*(range(3,d+1) for d in capacity)):
            if sum(hits)!=slots:
                continue
            saturation = {i for i,h in enumerate(hits) if h==capacity[i]}
            if len(saturation)<3:
                continue
            misses = tuple(saturation-neighbors[i]-{i} for i in range(order))
            if not all(misses):
                continue
            max_mark = tuple((r if r>=5 else 0)+sum(hits[j]+r>=10 for j in neighbors[i])
                             for i,r in enumerate(hits))
            if any(h==0 or (h<=5 and len(misses[i])==1) for i,h in enumerate(max_mark)):
                continue
            if any(max_mark[u]+max_mark[v]<13 and not misses[u]&misses[v]
                   for u,v in combinations(range(order),2)):
                continue
            if any(tuple(hits[i] for i in p)<hits for p in automorphisms):
                continue
            shapes.append((mask,hits))
    return tuple(shapes)


def ten_bundle_cases(witness_pairs,profiles,active_orders,outer_shapes):
    def parts(edges,vertices,start):
        if not edges:
            yield (0,)*vertices
            return
        for i in range(start,len(B10_SMALL_COMPONENTS)):
            n, es = B10_SMALL_COMPONENTS[i]
            if len(es)<=edges and n<=vertices:
                for rest in parts(edges-len(es),vertices-n,i):
                    yield tuple(sorted((i,)+rest))

    assert 0<=witness_pairs<=4
    exterior = 3*(30-2*witness_pairs)//14
    for parts_list in parts(witness_pairs,10,1):
        cyclic = [i for i,j in enumerate(parts_list)
                  if len(B10_SMALL_COMPONENTS[j][1])==B10_SMALL_COMPONENTS[j][0]]
        for bits in product((0,1),repeat=len(cyclic)):
            twist = tuple(bits[cyclic.index(i)] if i in cyclic else 0
                          for i in range(len(parts_list)))
            if tuple(zip(parts_list,twist))!=tuple(sorted(zip(parts_list,twist))):
                continue
            if profiles and witness_pairs in B10_PROFILES:
                for j,row in enumerate(B10_PROFILES[witness_pairs]):
                    yield "b10",parts_list,twist,len(row[0]),j
            elif outer_shapes:
                slots = 30-2*witness_pairs
                for n in range(5,exterior+1):
                    for shape in ten_outer_shapes(n,slots):
                        yield "b10",parts_list,twist,n,-1,True,shape
            elif active_orders:
                slots = 30-2*witness_pairs
                for n in range(max(3,(slots+7)//8),exterior+1):
                    yield "b10",parts_list,twist,n,-1,True
            else:
                yield "b10",parts_list,twist,exterior,-1


def cases(bundles,witness_pairs,profiles=False,active_orders=False,outer_shapes=False):
    if bundles==10:
        yield from ten_bundle_cases(witness_pairs,profiles,active_orders,outer_shapes)
        return
    exterior_slots = bundles*(13-bundles)-2*witness_pairs
    if exterior_slots < 0:
        return
    if 0 < exterior_slots < bundles:
        exterior = exterior_slots//(bundles-5)
        if not exterior or exterior_slots>8*exterior:
            return
    else:
        exterior = exterior_slots//(bundles-7)
    exterior = min(35-2*bundles,exterior)
    # This enumeration is used only for eleven repeated bundles.
    assert bundles == 11
    for path_total in range(bundles+1):
        for paths in partitions(path_total,1,bundles-witness_pairs):
            for cycles in partitions(bundles-path_total,3):
                for twists in product((0,1),repeat=len(cycles)):
                    if tuple(zip(cycles,twists)) != tuple(sorted(zip(cycles,twists))):
                        continue
                    if profiles and witness_pairs in EXTERIOR_PROFILES:
                        for index, row in enumerate(EXTERIOR_PROFILES[witness_pairs]):
                            yield paths,cycles,twists,len(row[0]),index
                    else:
                        yield paths,cycles,twists,exterior


def fixed_pairs(paths,cycles,twists):
    doubled = {}
    components = []
    first = 0
    for size, twist in [(k,None) for k in paths]+list(zip(cycles,twists)):
        stop = first+size
        components.append(tuple(range(first,stop)))
        for i in range(first,stop-1):
            doubled[i,i+1] = 0
        if twist is not None:
            doubled[first,stop-1] = twist
        first = stop
    return doubled,components


def fixed_ten_pairs(parts, twists):
    doubled,components = {},[]
    first = 0
    for part,twist in zip(parts,twists):
        size,edges = B10_SMALL_COMPONENTS[part]
        components.append(tuple(range(first,first+size)))
        sets = [{i} for i in range(size)]
        for u,v in edges:
            if sets[u]==sets[v]:
                direction = twist
            else:
                direction = 0
                joined = sets[u]|sets[v]
                for i in joined:
                    sets[i] = joined
            doubled[first+u,first+v] = direction
        first += size
    return doubled,components


def instance(bundles,witness_pairs,case,strengthened=False,exterior_saturation=False,
             deletion_cuts=False):
    if case[0]=="b10":
        _,parts,twists,exterior,profile = case[:5]
        ext_profile = B10_PROFILES[witness_pairs][profile] if profile>=0 else None
        if len(case)==7:
            mask,hits = case[-1]
            support = tuple(e for i,e in enumerate(combinations(range(exterior),2)) if mask>>i&1)
            ext_profile = hits,support,(),()
        fixed,components = fixed_ten_pairs(parts,twists)
        classes = tuple(zip(parts,twists))
    else:
        paths,cycles,twists,exterior = case[:4]
        ext_profile = EXTERIOR_PROFILES[witness_pairs][case[-1]] if len(case)==5 else None
        fixed,components = fixed_pairs(paths,cycles,twists)
        classes = tuple((n,None) for n in paths)+tuple(zip(cycles,twists))
    assert len(fixed)==witness_pairs
    core = 2*bundles
    n = core+exterior
    f = GraphCNF()
    yes,no = f.truth,-f.truth
    pairs = tuple(combinations(range(n),2))
    host,mark = {},{}
    for u,v in pairs:
        if v<core and u//2==v//2:
            h=m=yes
        elif v<core and (u//2,v//2) in fixed:
            h = yes if (u%2)^(v%2)==fixed[u//2,v//2] else no
            m = f.variable() if h==yes else no
        else:
            h,m = f.variable(),f.variable()
            f.clause(-m,h)
        host[u,v],mark[u,v] = h,m

    def at(table,u,v):
        return table[min(u,v),max(u,v)] if u!=v else no

    def adjacent(u,v):
        return at(host,u,v)

    def red(u,v):
        return at(mark,u,v)

    for i,j in combinations(range(bundles),2):
        if (i,j) in fixed:
            continue
        require_exactly(f,[adjacent(u,v) for u in (2*i,2*i+1) for v in (2*j,2*j+1)],1)
    if len(components)>1:
        # Both simultaneous endpoint flips preserve every fixed double witness
        # within a component. The first connection between components fixes them.
        base = components[0][0]
        first = components[1][0]
        f.clause(adjacent(2*base,2*first))
        for component in components[2:]:
            j = component[0]
            f.clause(adjacent(2*base,2*j),adjacent(2*base+1,2*j))
    else:
        i,j = next(pair for pair in combinations(range(bundles),2) if pair not in fixed)
        f.clause(adjacent(2*i,2*j),adjacent(2*i,2*j+1))
    if strengthened and len(components)>1:
        by_shape = {}
        base = components[0][0]
        for component,kind in zip(components[1:],classes[1:]):
            by_shape.setdefault(kind,[]).append(component[0])
        for shape in by_shape.values():
            for u,v in zip(shape,shape[1:]):
                f.clause(adjacent(2*base,2*u),-adjacent(2*base,2*v))

    for u in range(core,n):
        for i in range(bundles):
            f.clause(-adjacent(u,2*i),-adjacent(u,2*i+1))

    active = []
    external_degree = []
    hits = []
    saturated = []
    for u in range(n):
        d = [adjacent(u,v) for v in range(n) if v!=u]
        if u<core:
            require_exactly(f,d,7)
            external_degree.append(f.count([adjacent(u,v) for v in range(core,n)],exterior))
        else:
            f.at_most(d,8)
            if exterior_saturation:
                saturated.append(f.count(d,8)[8])
            active.append(f.any(red(u,v) for v in range(n) if u!=v))
            for v in range(n):
                f.clause(-adjacent(u,v),active[-1])
            hits.append(f.count([adjacent(u,v) for v in range(core)],8))
            f.clause(-active[-1],hits[-1][bundles-7])
            if ext_profile:
                target = ext_profile[0][u-core]
                f.clause(hits[-1][target])
                if target<8:
                    f.clause(-hits[-1][target+1])
    if ext_profile:
        _,required,red_required,optional = ext_profile
        for u,v in combinations(range(exterior),2):
            pair = u,v
            if pair not in optional:
                e = adjacent(u+core,v+core)
                f.clause(e if pair in required else -e)
            if pair in red_required:
                f.clause(red(u+core,v+core))
            if pair in optional:
                f.clause(-red(u+core,v+core))
    require_at_least(f,active,max(0,22-core))
    if case[0]=="b10" and len(case)>=6:
        for lit in active:
            f.clause(lit)
    if exterior_saturation:
        outer_min = bundles-7
        slots = bundles*(13-bundles)-2*witness_pairs
        require_at_least(f,saturated,3 if bundles<=10 else 2)
        if outer_min>2:
            f.at_most(active,(slots-20+2*outer_min)//(outer_min-2))
        for u in range(n):
            f.clause(*(f.conjunction(saturated[v-core],-adjacent(u,v))
                       for v in range(core,n) if v!=u))
    if deletion_cuts:
        assert exterior_saturation
        red_degree = [f.count([red(u,v) for v in range(n) if u!=v],9) for u in range(n)]
        for u,v in pairs:
            avoids = f.any(f.conjunction(saturated[w-core],
                          f.conjunction(-adjacent(u,w),-adjacent(v,w)))
                          for w in range(core,n) if w not in (u,v))
            for left in range(9):
                right = 23-bundles-left
                if right>=1:
                    f.clause(avoids,red_degree[u][left+1],
                             red_degree[v][right] if right<=8 else no)
                if right>=0:
                    f.clause(avoids,-red(u,v),red_degree[u][left+1],
                             red_degree[v][right+1] if right<8 else no)
    require_exactly(f,[adjacent(u,v) for u in range(core) for v in range(core,n)],
                    bundles*(13-bundles)-2*witness_pairs)

    marked_pairs = [pair for pair in pairs if mark[pair]!=no]
    require_exactly(f,[mark[pair] for pair in marked_pairs],81-bundles)
    for (u,v),(x,y) in combinations(marked_pairs,2):
        if u not in (x,y) and v not in (x,y):
            f.clause(-red(u,v),-red(x,y),*(adjacent(a,b) for a in (u,v) for b in (x,y)))
    for u,v,w in combinations(range(n),3):
        f.clause(-red(u,v),-red(u,w),-red(v,w))

    for u,v in marked_pairs:
        if strengthened:
            common = [f.conjunction(adjacent(u,w),adjacent(v,w)) for w in range(n)
                      if w not in (u,v)]
            if v<core:
                f.imply_at_most_one(red(u,v),common)
            else:
                union = [f.disjunction(adjacent(u,w),adjacent(v,w)) for w in range(n)
                         if w not in (u,v)]
                f.clause(-red(u,v),f.count(union,11)[11])
        if v<core and u//2!=v//2:
            f.clause(-red(u,v),-f.count(
                [adjacent(w,x) for w in (u,v) for x in range(core,n)],13-bundles
            )[13-bundles])
        elif u<core<=v:
            f.clause(-red(u,v),hits[v-core][bundles-5])
            for slots in range(2,min(7,exterior+1)):
                bound = bundles-6+slots
                f.clause(-red(u,v),-external_degree[u][slots],hits[v-core][bound] if bound<=8 else no)
        elif u>=core:
            for left in range(bundles-8,9):
                right = bundles-left
                if 1<=right<=8:
                    f.clause(-red(u,v),hits[u-core][left+1] if left<8 else no,
                             hits[v-core][right])

    for u in range(core,n-1 if not ext_profile else core):
        v = u+1
        previous = yes
        for x in range(n):
            if x in (u,v):
                continue
            for table in (mark,host):
                a,b = at(table,u,x),at(table,v,x)
                if a!=b:
                    f.clause(-previous,a,-b)
                    equal = f.disjunction(f.conjunction(a,b),f.conjunction(-a,-b))
                    previous = f.conjunction(previous,equal)
    return f


def case_name(witness_pairs,case):
    if case[0]=="b10":
        _,parts,twists,exterior,profile = case[:5]
        if len(case)==7:
            mask,hits = case[-1]
            suffix = f"n{exterior}_g{mask:x}_r{''.join(map(str,hits))}"
        else:
            suffix = f"n{exterior}" if len(case)==6 else f"x{profile}"
        return f"p{witness_pairs}_b{''.join(map(str,parts))}_t{''.join(map(str,twists))}_{suffix}"
    paths,cycles,twists,_ = case[:4]
    fields = [str(witness_pairs),"-".join(map(str,paths)), "-".join(map(str,cycles)),
              "".join(map(str,twists))]
    if len(case)==5:
        fields.append("x"+str(case[-1]))
    return "p"+"_".join(fields)


def run(args,witness_pairs,case):
    name = case_name(witness_pairs,case)
    log,result = (args.out/(name+s) for s in (".log",".result.json"))
    if result.exists():
        saved = json.loads(result.read_text())
        if saved["result"]=="VERIFIED_UNSAT":
            return saved
    if args.scratch_root:
        workspace = TemporaryDirectory(prefix="fgst_d8_repeat_",dir=args.scratch_root)
    else:
        workspace = nullcontext(args.out)
    with workspace as directory:
        directory = Path(directory).resolve()
        if args.scratch_root:
            assert directory.is_relative_to(args.scratch_root)
        cnf,proof = (directory/(name+s) for s in (".cnf",".lrat"))
        instance(args.bundles,witness_pairs,case,args.strengthened,args.exterior_saturation,
                 args.deletion_cuts).dump(cnf)
        code,limit = bounded_solve(args.solver,cnf,proof,log,args.timeout,args.max_proof_mib*1024**2)
        row = dict(name=name,witness_pairs=witness_pairs,case=case,bundles=args.bundles,
                   strengthened=args.strengthened,
                   exterior_saturation=args.exterior_saturation,
                   deletion_cuts=args.deletion_cuts,
                   result="SAT" if code==10 else "UNKNOWN",limit=limit)
        if code==20:
            check = subprocess.run([str(args.checker),cnf.name,proof.name],cwd=directory,
                                   capture_output=True,text=True,check=True)
            row.update(result="VERIFIED_UNSAT",replay=json.loads(check.stdout),
                       cnf_sha256=file_digest(cnf),lrat_sha256=file_digest(proof))
            for path in (cnf,proof):
                if args.scratch_root:
                    with path.open("rb") as source, (args.out/(path.name+".gz")).open("wb") as target:
                        with gzip.GzipFile(filename="",fileobj=target,mode="wb",
                                           compresslevel=4,mtime=0) as packed:
                            shutil.copyfileobj(source,packed)
                else:
                    gzip_file(path)
        elif code!=10 and proof.exists():
            proof.unlink()
    result.write_text(json.dumps(row,indent=2)+"\n")
    print(name,row["result"],limit or "",flush=True)
    return row


def replay(args,witness_pairs,case):
    name = case_name(witness_pairs,case)
    row = json.loads((args.out/(name+".result.json")).read_text())
    if row["result"]!="VERIFIED_UNSAT" or row["bundles"]!=args.bundles:
        raise ValueError(f"{name}: missing fixed proof")
    with TemporaryDirectory(prefix="fgst_repeat_core_",dir=args.out) as tmp:
        scratch = Path(tmp)
        regenerated,cnf,proof = (scratch/file for file in ("new.cnf","fixed.cnf","fixed.lrat"))
        instance(args.bundles,witness_pairs,case,row.get("strengthened",False),
                 row.get("exterior_saturation",False),row.get("deletion_cuts",False)).dump(regenerated)
        if file_digest(regenerated)!=row["cnf_sha256"]:
            raise ValueError(f"{name}: regenerated CNF differs")
        for target, suffix, key in ((cnf,".cnf.gz","cnf_sha256"),
                                    (proof,".lrat.gz","lrat_sha256")):
            if unpack(args.out/(name+suffix),target)!=row[key]:
                raise ValueError(f"{name}: archived {suffix} differs")
        result = subprocess.run([str(args.checker),cnf.name,proof.name],cwd=scratch,
                                capture_output=True,text=True,check=True)
    row["replay"] = json.loads(result.stdout)
    assert row["replay"]["added"] > 0
    print(name,row["replay"]["added"],"verified RUP additions",flush=True)
    return row


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--witness-pairs",nargs="+",type=int,required=True)
    parser.add_argument("--bundles",type=int,default=11)
    parser.add_argument("--jobs",type=int,default=3)
    parser.add_argument("--timeout",type=int,default=90)
    parser.add_argument("--max-proof-mib",type=int,default=125)
    parser.add_argument("--out",type=Path,required=True)
    parser.add_argument("--solver",type=Path)
    parser.add_argument("--checker",type=Path,default=Path("d7_rup_replay.exe"))
    parser.add_argument("--scratch-root",type=Path)
    parser.add_argument("--verify",action="store_true")
    parser.add_argument("--strengthened",action="store_true")
    parser.add_argument("--exterior-saturation",action="store_true")
    parser.add_argument("--exterior-profiles",action="store_true")
    parser.add_argument("--active-orders",action="store_true")
    parser.add_argument("--outer-shapes",action="store_true")
    parser.add_argument("--deletion-cuts",action="store_true")
    parser.add_argument("--select",nargs="+")
    parser.add_argument("--report",type=Path)
    args = parser.parse_args()
    args.out,args.checker = args.out.resolve(),args.checker.resolve()
    if args.scratch_root:
        args.scratch_root = args.scratch_root.resolve()
        args.scratch_root.mkdir(parents=True,exist_ok=True)
    if not args.verify and not args.solver:
        parser.error("supply --solver or --verify")
    if args.solver:
        args.solver = args.solver.resolve()
    task = replay if args.verify else run
    selected = [(p,c) for p in args.witness_pairs
                for c in cases(args.bundles,p,args.exterior_profiles,args.active_orders,
                               args.outer_shapes)
                if not args.select or case_name(p,c) in args.select]
    if not selected:
        parser.error("no templates selected")
    args.out.mkdir(parents=True,exist_ok=True)
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        rows = list(pool.map(lambda pair:task(args,*pair),selected))
    report = dict(verified=all(row["result"]=="VERIFIED_UNSAT" for row in rows),
                  templates=len(rows),instances=rows)
    if args.report:
        args.report.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(dict(templates=len(rows),fixed=sum(
        row["result"]=="VERIFIED_UNSAT" for row in rows
    ))),flush=True)


if __name__=="__main__":
    main()
