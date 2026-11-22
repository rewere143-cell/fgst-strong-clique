"""D9 n23 finite instances with triangle-free saturated marked support."""
from concurrent.futures import ThreadPoolExecutor
from itertools import combinations, combinations_with_replacement
from pathlib import Path
import argparse
import json
import subprocess

from d7_parallel_sat import GraphCNF, file_digest


def all_cases():
    for k in range(8,12):
        for deficit in combinations_with_replacement(range(1,9),k):
            if sum(deficit)!=11:
                continue
            name="k"+str(k)+"_"+"".join(map(str,deficit))
            s=23-k
            for p in range(s-9,s//2+1):
                yield name+"_b"+str(p),deficit,p
            yield name+"_c",deficit,None


def instance(deficit,split):
    k=len(deficit)
    s=23-k
    A,U=range(s),range(s,23)
    d=[9]*s+[9-x for x in deficit]
    f=GraphCNF()
    yes,no=f.truth,-f.truth
    pairs=list(combinations(range(23),2))
    mark,host={},{}
    for x,y in pairs:
        mark[x,y]=f.variable()
        host[x,y]=mark[x,y] if x<s else f.variable()
        f.clause(-mark[x,y],host[x,y])

    def get(tab,x,y):
        return no if x==y else tab[min(x,y),max(x,y)]

    full={}
    for x in range(23):
        hs=f.count([get(host,x,y) for y in range(23) if y!=x],10)
        f.clause(-hs[10])
        full[x]=hs[9]
        ds=f.count([get(mark,x,y) for y in range(23) if y!=x],d[x]+1)
        f.clause(ds[d[x]])
        f.clause(-ds[d[x]+1])
    f.at_most([f.conjunction(host[x,y],-mark[x,y]) for x,y in combinations(U,2)],5)

    for e,e2 in combinations(pairs,2):
        if len(set(e+e2))==4:
            f.clause(-mark[e],-mark[e2],*(get(host,a,b) for a in e for b in e2))

    # Deleting any two vertices would retain at least 80 marked edges. With
    # host degree <=8, equality would require just 20 marked support points,
    # but each of the 21 remaining vertices retains positive marked degree.
    for x,y in pairs:
        f.clause(*(f.conjunction(full[z],f.conjunction(-get(host,x,z),-get(host,y,z)))
                   for z in range(23) if z not in (x,y)))

    tri=[]
    for x,y,z in combinations(range(23),3):
        if z>=s:
            tri.append(f.conjunction(mark[x,y],f.conjunction(mark[x,z],mark[y,z])))
    cap=(156-sum(d[x]*(9-d[x]) for x in U))//6
    f.at_most(tri,cap)

    if split is not None:
        for x,y in combinations(A,2):
            if y<split or x>=split:
                f.clause(-mark[x,y])
        for x in range(split):
            for y in range(split,s):
                if x+1<split:
                    f.clause(-mark[x+1,y],mark[x,y])
                if y+1<s:
                    f.clause(-mark[x,y+1],mark[x,y])
    else:
        part=[]
        for x in A:
            if x<5:
                part.append([yes if j==x else no for j in range(6)])
            else:
                v=[f.variable() for _ in range(6)]
                f.clause(*v)
                f.at_most(v,1)
                part.append(v)
        for x,y in combinations(A,2):
            for i in range(6):
                for j in range(6):
                    v=mark[x,y] if max(i,j)<5 and (i-j)%5 in (1,4) else -mark[x,y]
                    f.clause(-part[x][i],-part[y][j],v)
        for x in range(5,s-1):
            for i in range(6):
                for j in range(i):
                    f.clause(-part[x][i],-part[x+1][j])
    for x in range(s,22):
        y=x+1
        if d[x]!=d[y]:
            continue
        prefix=yes
        for z in range(23):
            if z in (x,y):
                continue
            for tab in (mark,host):
                a,b=get(tab,x,z),get(tab,y,z)
                if a==b:
                    continue
                f.clause(-prefix,a,-b)
                prefix=f.conjunction(prefix,f.disjunction(f.conjunction(a,b),f.conjunction(-a,-b)))
    return f


def run(args,case):
    name,deficit,split=case
    path=args.out/(name+".cnf")
    proof=args.out/(name+".lrat")
    f=instance(deficit,split)
    f.dump(path)
    result=dict(name=name,clauses=len(f.clauses),variables=f.variables,
                cnf_sha256=file_digest(path))
    with (args.out/(name+".log")).open("wb") as log:
        try:
            status=subprocess.run([str(args.solver),"--lrat","--no-binary",str(path),str(proof)],
                                  stdout=log,stderr=subprocess.STDOUT,timeout=args.timeout).returncode
        except subprocess.TimeoutExpired:
            status=None
    result["code"]=status
    if status==20:
        replay=subprocess.run([str(args.checker),path.name,proof.name],cwd=args.out,
                              check=True,capture_output=True,text=True)
        result.update(replay=json.loads(replay.stdout),lrat_sha256=file_digest(proof))
    (args.out/(name+".json")).write_text(json.dumps(result)+"\n")
    print(result,flush=True)
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out",type=Path,required=True)
    parser.add_argument("--solver",type=Path,required=True)
    parser.add_argument("--checker",type=Path,required=True)
    parser.add_argument("--jobs",type=int,default=2)
    parser.add_argument("--timeout",type=int,default=90)
    args=parser.parse_args()
    args.out.mkdir(parents=True,exist_ok=True)
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        results=list(pool.map(lambda case:run(args,case),all_cases()))
    (args.out/"summary.json").write_text(json.dumps(results,indent=2)+"\n")


if __name__=="__main__":
    main()

