"""Fixed blue graph and Ferrers chain CNFs for 98 marks at order 23."""

import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from dataclasses import asdict, dataclass
from functools import cache
from itertools import combinations, permutations, product
import json
from pathlib import Path
import sys
from tempfile import TemporaryDirectory

sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
PARENT=HERE.parent
sys.path[:0]=[str(PARENT),str(PARENT/"三小时续研_有限度数")]

from d7_parallel_sat import GraphCNF, file_digest
from d7_verify_parallel import unpack
from d8_b9_sat import check_replay, initial_conflict, lex_maximum
from d8_parallel_sat import bounded_solve, gzip_file
from d8_repeat_core_sat import require_at_least, require_exactly


@cache
def connected_types(edges_count):
    """All connected simple types with the specified positive edge count."""
    found=[]
    for n in range(2,edges_count+2):
        pairs=tuple(combinations(range(n),2))
        if len(pairs)<edges_count:
            continue
        canon=set()
        for edges in combinations(pairs,edges_count):
            adjacency=[set() for _ in range(n)]
            for u,v in edges:
                adjacency[u].add(v)
                adjacency[v].add(u)
            seen={0}
            queue=[0]
            for v in queue:
                new=adjacency[v]-seen
                seen.update(new)
                queue.extend(sorted(new))
            if len(seen)!=n:
                continue
            degrees=Counter(map(len,adjacency))
            degree_parts=[[v for v in range(n) if len(adjacency[v])==d]
                          for d in sorted(degrees,reverse=True)]
            variants=[]
            for block_order in product(*(permutations(part) for part in degree_parts)):
                ordering=tuple(v for part in block_order for v in part)
                mapping={v:i for i,v in enumerate(ordering)}
                variants.append(tuple(sorted(tuple(sorted((mapping[u],mapping[v]))) for u,v in edges)))
            canon.add(min(variants))
        for e in sorted(canon):
            found.append((n,e))
    return tuple(found)


@cache
def blue_types(edge_budget):
    catalogue=tuple((m,n,g) for m in range(1,edge_budget+1) for n,g in connected_types(m))
    items=[]
    def combine(start,rem,selection):
        if rem==0:
            edges=[]
            components=[]
            offset=0
            for n,comp in selection:
                edges.extend((u+offset,v+offset) for u,v in comp)
                components.append((offset,n,comp))
                offset+=n
            items.append((offset,tuple(edges),tuple(components)))
            return
        for j in range(start,len(catalogue)):
            m,n,comp=catalogue[j]
            if m>rem:
                break
            combine(j,rem-m,selection+((n,comp),))
    combine(0,edge_budget,())
    return tuple(sorted(items,key=lambda x:(x[0],x[1])))


@dataclass(frozen=True)
class Case:
    order: int
    beta: int
    blue_id: int
    blue_order: int
    blue: tuple
    components: tuple
    left: int
    right: int
    isolates: int
    min_internal: int
    min_cover: int
    rows: tuple = ()
    degrees: tuple = ()

    @property
    def name(self):
        fixed="" if not self.rows else "_r"+"".join(map(str,self.rows))
        shape="d"+"".join(map(str,self.degrees)) if self.degrees else f"{self.blue_id:02d}"
        return f"n{self.order}_b{self.beta}_{shape}_k{self.blue_order}_{self.left}x{self.right}_i{self.isolates}{fixed}"


def cover_lower(left,right,min_edges):
    best=min(left,right)
    for r in range(1,left):
        for s in range(1,right):
            if left*right-(left-r)*(right-s)>=min_edges:
                best=min(best,r+s)
    return best


def admissible_isolates(nodes,blue,isolates,tau,slack,degrees=()):
    degree=degrees or [sum(v in uv for uv in blue) for v in range(nodes)]
    possible=sum(max(0,min(9-deg-tau,2*isolates,isolates+2)) for deg in degree)
    return possible>=9*isolates-slack


def row_profiles(left,right,min_edges):
    def recurse(prefix,last,remaining):
        if remaining==0:
            if sum(prefix)>=min_edges:
                yield prefix
            return
        for value in range(last,0,-1):
            if sum(prefix)+remaining*value>=min_edges:
                yield from recurse(prefix+(value,),value,remaining-1)
    yield from recurse((right,),right,left-1)


def degree_shapes(beta,max_order):
    def partitions(total,remaining,upper):
        if remaining==0:
            if total==0:
                yield ()
            return
        if total<remaining or total>remaining*upper:
            return
        for first in range(min(upper,total-remaining+1),max(1,(total+remaining-1)//remaining)-1,-1):
            for rest in partitions(total-first,remaining-1,first):
                yield (first,)+rest
    def graphical(d):
        return all(sum(d[:j])<=j*(j-1)+sum(min(j,x) for x in d[j:])
                   for j in range(1,len(d)+1))
    return [(k,(),(),d) for k in range(2,min(max_order,2*beta)+1)
            if k*(k-1)//2>=beta
            for d in partitions(2*beta,k,min(k-1,8)) if graphical(d)]


def cases(order,betas,endpoint_counts=None,*,fix_rows=False,degree_profiles=False,repeat_min=1):
    for beta in betas:
        slack=9*order-196-2*beta
        if slack<0:
            continue
        if degree_profiles:
            all_types=degree_shapes(beta,order)
        elif beta>8:
            from d9_blue_shape_extension import high_endpoint_types
            all_types=[(*r,()) for r in high_endpoint_types(beta,tuple(endpoint_counts))]
        elif beta>5:
            from d9_blue_shape_extension import blue_types as larger
            all_types=[(*r,()) for r in larger(beta)]
        else:
            all_types=[(*r,()) for r in blue_types(beta)]
        for blue_id,(k,blue,components,degrees) in enumerate(all_types,1):
            if endpoint_counts is not None and k not in endpoint_counts:
                continue
            if k>order:
                continue
            if repeat_min>1:
                b_degree=degrees or tuple(sum(v in e for e in blue) for v in range(k))
                if sum(min(2,(9-x)//2) for x in b_degree)<repeat_min:
                    continue
            min_m=98-9*k+2*beta
            if min_m<=0 and not fix_rows:
                i=order-k
                if admissible_isolates(k,blue,i,0,slack,degrees):
                    yield Case(order,beta,blue_id,k,blue,components,0,0,i,0,0,(),degrees)
            for left in range(1,10):
                for right in range(left,10):
                    i=order-k-left-right
                    if i<0 or left*right<min_m:
                        continue
                    minimum_cover=cover_lower(left,right,max(1,min_m))
                    if not admissible_isolates(k,blue,i,minimum_cover,slack,degrees):
                        continue
                    profiles=row_profiles(left,right,max(1,min_m)) if fix_rows else ((),)
                    for rows in profiles:
                        tau=min([left]+[q+r for q,r in enumerate(rows)]) if rows else minimum_cover
                        if not admissible_isolates(k,blue,i,tau,slack,degrees):
                            continue
                        yield Case(order,beta,blue_id,k,blue,components,left,right,i,max(0,min_m),tau,rows,degrees)


def automorphisms(components):
    # It suffices to compare along any list of allowed permutations: an
    # overall lexicographic maximum satisfies all of them simultaneously.
    earlier={}
    for offset,n,edges in components:
        for order in permutations(range(n)):
            if order==tuple(range(n)):
                continue
            moved=tuple(sorted(tuple(sorted((order[u],order[v]))) for u,v in edges))
            if moved==edges:
                yield {offset+i:offset+j for i,j in enumerate(order) if i!=j}
        same=(n,edges)
        if same in earlier:
            old=earlier[same]
            yield {**{offset+i:old+i for i in range(n)},**{old+i:offset+i for i in range(n)}}
        earlier[same]=offset


def lex_when(f,condition,left,right):
    equal=condition
    for a,b in zip(left,right):
        if a==b:
            continue
        f.clause(-equal,a,-b)
        same=f.disjunction(f.conjunction(a,b),f.conjunction(-a,-b))
        equal=f.conjunction(equal,same)


def formula(case,*,triangles=True, repeat_union=True, repeat_min=1, repeat_max=18,
            four_saturated=False, required_c5=False, anchor_core_cap=None):
    f=GraphCNF()
    yes,no=f.truth,-f.truth
    n=case.order
    vertices=range(n)
    B=range(case.blue_order)
    A=range(B.stop,B.stop+case.left)
    C=range(A.stop,A.stop+case.right)
    I=range(C.stop,n)
    blue=set(case.blue)
    pairs=tuple(combinations(vertices,2))
    host,mark,double,fixed_blue={},{},{},{}
    possible=[]
    for u,v in pairs:
        if case.degrees and v in B:
            h,r,d,b=(f.variable() for _ in range(4))
            f.clause(-d,r)
            f.clause(-r,h)
            f.clause(-b,h)
            f.clause(-h,r,b)
            f.clause(-r,-b)
            fixed_blue[u,v]=b
        elif (u,v) in blue:
            h,r,d=yes,no,no
        elif u in B:
            h=r=f.variable()
            d=f.variable()
            f.clause(-d,r)
        elif u in A and v in C:
            if case.rows:
                h=r=yes if v-C.start<case.rows[u-A.start] else no
            else:
                h=r=yes if u==A.start or v==C.start else f.variable()
            d=no
        else:
            h=r=d=no
        host[u,v],mark[u,v],double[u,v]=h,r,d
        if r!=no:
            possible.append((u,v))

    def lit(table,u,v):
        return no if u==v else table[min(u,v),max(u,v)]

    if not case.rows:
        for u,v in product(A,C):
            if u!=A.start:
                f.clause(-host[u,v],host[u-1,v])
            if v!=C.start:
                f.clause(-host[u,v],host[u,v-1])
        require_at_least(f,[mark[u,v] for u,v in product(A,C)],case.min_internal)
    if I:
        for b in B:
            covers=f.count([mark[b,u] for u in tuple(A)+tuple(C)],case.min_cover)[case.min_cover]
            for z in I:
                f.clause(-mark[b,z],covers)

    degree,projection,repeat_degree = {},{},{}
    full_simple={}
    host_deficits=[]
    slack=9*n-196-2*case.beta
    blue_degree=list(case.degrees)+[0]*(n-len(B)) if case.degrees else [
        sum(u in uv for uv in blue) for u in vertices]
    for u in vertices:
        h=[lit(host,u,v) for v in vertices if v!=u]
        r=[lit(mark,u,v) for v in vertices if v!=u]
        d=[lit(double,u,v) for v in vertices if v!=u]
        caps=9-blue_degree[u]
        marked_degree=f.count(r+d,caps+1)
        actual=f.count(h,9)
        degree[u]=marked_degree[caps]
        projection[u]=actual[9 if n==24 else 8]
        full_simple[u]=actual[9]
        # For n=23 we additionally need the exact simple-nine threshold.
        if n==23:
            projection[u]=(actual[8],actual[9])
        repeat_degree[u]=f.count(d,3)
        f.clause(-marked_degree[caps+1])
        f.clause(marked_degree[max(1,caps-slack)])
        f.clause(-repeat_degree[u][3])
        host_deficits.extend(-d for d in marked_degree[1:caps+1])
        if case.degrees and u in B:
            require_exactly(f,[lit(fixed_blue,u,v) for v in B if v!=u],blue_degree[u])
    require_exactly(f,host_deficits,slack)
    require_at_least(f,list(double.values()),repeat_min)
    f.at_most(list(double.values()),repeat_max)

    for index,uv in enumerate(possible):
        u,v=uv
        outside=[x for x in vertices if x not in uv]
        if repeat_union or double[uv]!=no:
            union=[f.disjunction(lit(host,u,x),lit(host,v,x)) for x in outside]
            thresholds=f.count(union,13 if double[uv]!=no else 11)
            if repeat_union:
                f.clause(-mark[uv],thresholds[11])
            if double[uv]!=no:
                f.clause(-double[uv],thresholds[13])
                f.clause(-double[uv],-repeat_degree[u][2],-repeat_degree[v][2])
        for xy in possible[index+1:]:
            if len(set(uv+xy))==4:
                f.clause(-mark[uv],-mark[xy],
                         *(lit(host,a,b) for a,b in product(uv,xy)))

    for u,v in pairs:
        f.clause(*(f.conjunction(degree[x],f.conjunction(-lit(host,u,x),-lit(host,v,x)))
                   for x in vertices if x not in (u,v)))

    triangle_literals=[]
    for tri in combinations(vertices,3):
        flags=[mark[uv] for uv in combinations(tri,2)]
        if no in flags:
            continue
        q=sum(blue_degree[u] for u in tri)
        if not triangles or q not in (range(1,4) if n==23 else range(2,6)):
            f.clause(*(-r for r in flags))
            continue
        t=f.conjunction(flags[0],f.conjunction(flags[1],flags[2]))
        triangle_literals.append(t)
        for uv in combinations(tri,2):
            f.clause(-t,-double[uv])
        for u in tri:
            f.clause(-t,projection[u][0] if n==23 else projection[u])
        if n==23:
            for u,v in combinations(tri,2):
                f.clause(-t,projection[u][1],projection[v][1])
        common=[]
        for x in vertices:
            if x in tri:
                continue
            h=[lit(host,u,x) for u in tri]
            f.clause(-t,*h)
            if n==24:
                for i,j in combinations(range(3),2):
                    f.clause(-t,-h[i],-h[j])
            else:
                f.clause(-t,*(-a for a in h))
                common.append(f.count(h,2)[2])
        if n==23:
            f.imply_at_most_one(t,common)
    if triangles:
        f.clause(*triangle_literals)
    if four_saturated and A and C:
        univ_a,univ_c=A.start,C.start
        for a,c in product(range(univ_a+1,A.stop),range(univ_c+1,C.stop)):
            pre=(host[a,c],-full_simple[a],-full_simple[c],
                 -full_simple[univ_a],-full_simple[univ_c])
            for b in B:
                f.clause(*pre,-mark[b,a],-mark[b,c])
    if required_c5:
        point={(i,v):f.variable() for i,v in product(range(5),vertices)}
        for i in range(5):
            allowed=B if i==0 else vertices
            if i==0:
                for v in range(B.stop,n):
                    f.clause(-point[i,v])
            f.clause(*(point[i,v] for v in allowed))
            f.imply_at_most_one(yes,[point[i,v] for v in allowed])
        for v in vertices:
            f.imply_at_most_one(yes,[point[i,v] for i in range(5)])
        for i,j in combinations(range(5),2):
            consecutive=(j-i) in (1,4)
            for v,w in product(vertices,repeat=2):
                if v!=w:
                    relation=lit(mark,v,w) if consecutive else -lit(host,v,w)
                    f.clause(-point[i,v],-point[j,w],relation)
        if anchor_core_cap is not None:
            core=[]
            for v in vertices:
                host_to=[]
                red_to=[]
                for i in range(5):
                    host_to.append(f.any([f.conjunction(point[i,w],lit(host,v,w))
                                          for w in vertices if w!=v]))
                    red_to.append(f.any([f.conjunction(point[i,w],lit(mark,v,w))
                                         for w in vertices if w!=v]))
                signatures=[]
                for i in range(5):
                    a,b=(i-1)%5,(i+1)%5
                    sig=f.conjunction(red_to[a],red_to[b])
                    for j in range(5):
                        if j not in (a,b):
                            sig=f.conjunction(sig,-host_to[j])
                    signatures.append(sig)
                core.append(f.any(signatures))
            f.at_most(core,anchor_core_cap)

    layout=list(product(B,range(B.stop,n)))+list(combinations(B,2))
    tables=(mark,double,host) if case.degrees else (mark,double)
    word=[lit(table,u,v) for u,v in layout for table in tables]
    if case.degrees:
        actions=({u:u+1,u+1:u} for u in range(B.stop-1)
                 if blue_degree[u]==blue_degree[u+1])
    elif case.beta<=5:
        actions=automorphisms(case.components)
    else:
        from d9_blue_shape_extension import symmetry_actions
        actions=symmetry_actions(case.components)
    for p in actions:
        rival=[lit(table,p.get(u,u),p.get(v,v)) for u,v in layout for table in tables]
        lex_maximum(f,word,rival)
    for part,opposite in ((A,C),(C,A),(I,())):
        for x,y in zip(part,range(part.start+1,part.stop)):
            same=yes
            for z in opposite:
                a,b=lit(host,x,z),lit(host,y,z)
                if a!=b:
                    equivalent=f.disjunction(f.conjunction(a,b),f.conjunction(-a,-b))
                    same=f.conjunction(same,equivalent)
            lex_when(f,same,[lit(table,b,x) for b in B for table in tables],
                            [lit(table,b,y) for b in B for table in tables])
    return f


def run(args,case):
    name=case.name
    cnf,proof,log,status=(args.out/(name+s) for s in (".cnf",".lrat",".log",".json"))
    if status.exists() and not args.verify:
        prior=json.loads(status.read_text())
        if prior["result"]=="VERIFIED_UNSAT":
            return prior
    f=formula(case,triangles=not args.triangle_free,repeat_union=not args.only_repeated_union,
              repeat_min=args.repeat_min,repeat_max=args.repeat_max,
              four_saturated=args.four_saturated,required_c5=args.required_c5,
              anchor_core_cap=args.anchor_core_cap)
    if args.verify:
        row=json.loads(status.read_text())
        if row["result"]!="VERIFIED_UNSAT":
            raise ValueError(f"{name} has no verified proof")
        with TemporaryDirectory(dir=args.out) as directory:
            temp=Path(directory)
            regen,fixed,replay=(temp/n for n in ("regenerated.cnf","fixed.cnf","fixed.lrat"))
            f.dump(regen)
            if file_digest(regen)!=row["cnf_sha256"]:
                raise ValueError(f"{name} regenerated CNF mismatch")
            if unpack(cnf.with_suffix(".cnf.gz"),fixed)!=row["cnf_sha256"]:
                raise ValueError(f"{name} archived CNF mismatch")
            if unpack(proof.with_suffix(".lrat.gz"),replay)!=row["lrat_sha256"]:
                raise ValueError(f"{name} archived LRAT mismatch")
            if check_replay(temp,fixed,replay,args.checker)!=row["replay"]:
                raise ValueError(f"{name} replay count mismatch")
    else:
        f.dump(cnf)
        hints=initial_conflict(f.clauses)
        if hints:
            proof.write_text(f"{len(f.clauses)+1} 0 "+" ".join(map(str,hints))+" 0\n")
            log.write_text("The input has a unit contradiction.\n")
            code,limit=20,None
        else:
            code,limit=bounded_solve(args.solver,cnf,proof,log,args.timeout,args.proof_mib*1024**2)
        row=dict(name=name,case=asdict(case),variables=f.variables,clauses=len(f.clauses),
                 limit=limit,result="SAT" if code==10 else "UNKNOWN")
        if code==20:
            row.update(result="VERIFIED_UNSAT",cnf_sha256=file_digest(cnf),
                       lrat_sha256=file_digest(proof),replay=check_replay(args.out,cnf,proof,args.checker))
            gzip_file(cnf)
            gzip_file(proof)
        elif code!=10 and proof.exists():
            proof.unlink()
        status.write_text(json.dumps(row,indent=2)+"\n")
    print(name,row["result"],row.get("limit") or "",row["variables"],row["clauses"],flush=True)
    return row


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--out",type=Path,default=HERE/"chain_ferrers")
    p.add_argument("--solver",type=Path)
    p.add_argument("--checker",type=Path,default=PARENT/"d7_rup_replay.exe")
    p.add_argument("--verify",action="store_true")
    p.add_argument("--jobs",type=int,default=1)
    p.add_argument("--timeout",type=int,default=180)
    p.add_argument("--proof-mib",type=int,default=140)
    p.add_argument("--order",type=int,choices=(23,24,25),default=23)
    p.add_argument("--beta",nargs="+",type=int,choices=tuple(range(1,15)),default=tuple(range(1,6)))
    p.add_argument("--endpoints",nargs="+",type=int)
    p.add_argument("--triangle-free",action="store_true")
    p.add_argument("--repeat-min",type=int,default=1)
    p.add_argument("--repeat-max",type=int,default=18)
    p.add_argument("--four-saturated",action="store_true")
    p.add_argument("--required-c5",action="store_true")
    p.add_argument("--anchor-core-cap",type=int)
    p.add_argument("--degree-profiles",action="store_true")
    p.add_argument("--only-repeated-union",action="store_true")
    p.add_argument("--fix-rows",action="store_true")
    p.add_argument("--select",nargs="+")
    p.add_argument("--list",action="store_true")
    args=p.parse_args()
    if (args.order==25 or args.four_saturated) and not args.triangle_free:
        p.error("this option requires --triangle-free")
    if any(b>8 for b in args.beta) and not args.degree_profiles:
        if args.endpoints is None or any(2*b-k>7 for b in args.beta if b>8
                                         for k in args.endpoints if k<=2*b):
            p.error("use --degree-profiles or restrict endpoint excess to at most seven")
    if args.anchor_core_cap is not None and not args.required_c5:
        p.error("--anchor-core-cap requires --required-c5")
    entries=[x for x in cases(args.order,args.beta,args.endpoints,fix_rows=args.fix_rows,
                              degree_profiles=args.degree_profiles,repeat_min=args.repeat_min)
             if args.select is None or x.name in args.select]
    if args.list:
        for c in entries:
            print(c.name,c.blue,c.min_internal,c.min_cover)
        print("total",len(entries))
        return
    if not args.verify and not args.solver:
        p.error("provide the proof solver or use --verify")
    args.out=args.out.resolve()
    args.out.mkdir(exist_ok=True,parents=True)
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        results=list(pool.map(lambda case:run(args,case),entries))
    print(json.dumps({r["name"]:r["result"] for r in results},indent=2))


if __name__=="__main__":
    main()
