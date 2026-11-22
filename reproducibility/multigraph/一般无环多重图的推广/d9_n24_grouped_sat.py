"""Grouped exact D9/n24 search after the saturated-triangle reduction."""
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
from itertools import combinations
from pathlib import Path
import argparse
import gzip
import json
import shutil
import subprocess

from d7_parallel_sat import GraphCNF, file_digest


def xor(f, a, b):
    if a==b:
        return -f.truth
    if a==-b:
        return f.truth
    if a==f.truth or b==-f.truth:
        return -b if a==f.truth else a
    if b==f.truth or a==-f.truth:
        return -a if b==f.truth else b
    z=f.variable()
    f.clause(-z,a,b)
    f.clause(-z,-a,-b)
    f.clause(z,a,-b)
    f.clause(z,-a,b)
    return z


def weight_cap(f, terms, cap):
    """Encode sum of nonnegative integer weights times Boolean literals <= cap."""
    columns=[]
    for lit,w in terms:
        if lit==-f.truth:
            continue
        if lit==f.truth:
            cap-=w
            continue
        for j in range(w.bit_length()):
            if w>>j&1:
                while j>=len(columns):
                    columns.append([])
                columns[j].append(lit)
    if cap<0:
        f.clause()
        return
    for j,col in enumerate(columns):
        carry=[]
        while len(col)>=3:
            a,b,c=col.pop(),col.pop(),col.pop()
            ab=xor(f,a,b)
            col.append(xor(f,ab,c))
            carry.append(f.disjunction(f.conjunction(a,b),f.conjunction(ab,c)))
        if len(col)==2:
            a,b=col.pop(),col.pop()
            col.append(xor(f,a,b))
            carry.append(f.conjunction(a,b))
        if carry:
            if j+1==len(columns):
                columns.append([])
            columns[j+1].extend(carry)
    prefix=f.truth
    for j in range(len(columns)-1,-1,-1):
        bit=columns[j][0] if columns[j] else -f.truth
        if cap>>j&1:
            prefix=f.conjunction(prefix,bit)
        else:
            f.clause(-prefix,-bit)
            prefix=f.conjunction(prefix,-bit)


def triangle_cap(k):
    # Convexity: put excess deficit in one vertex up to 8 before the next.
    excess=20-k
    squares=k
    while excess:
        add=min(excess,7)
        squares+=(1+add)**2-1
        excess-=add
    return (squares-24)//6


def instance(k, shape, use_weight=True, fixed=None):
    n=24
    s=n-k
    f=GraphCNF()
    yes,no=f.truth,-f.truth
    A,U=range(s),range(s,n)
    pairs=tuple(combinations(range(n),2))
    mark,host = {},{}
    for i,j in pairs:
        m=f.variable()
        e=m if i<s else f.variable()
        f.clause(-m,e)
        mark[i,j],host[i,j]=m,e

    def get(table,x,y):
        return no if x==y else table[min(x,y),max(x,y)]

    ds,hs={},{}
    for v in range(n):
        ds[v]=f.count([get(mark,v,u) for u in range(n) if u!=v],10)
        hs[v]=ds[v] if v<s else f.count([get(host,v,u) for u in range(n) if u!=v],10)
        f.clause(-hs[v][10])
        if v<s:
            f.clause(ds[v][9])
        elif fixed is None:
            f.clause(ds[v][1])
            f.clause(-ds[v][9])
        else:
            h=9-fixed[v-s]
            f.clause(ds[v][h])
            f.clause(-ds[v][h+1])
    if fixed is None:
        deficit=[-ds[v][10-j] for v in U for j in range(1,9)]
        totals=f.count(deficit,21)
        f.clause(totals[20])
        f.clause(-totals[21])

    f.at_most([f.conjunction(host[i,j],-mark[i,j]) for i,j in combinations(U,2)],10)
    for e,g in combinations(pairs,2):
        if len(set(e+g))==4:
            f.clause(-mark[e],-mark[g],*(get(host,i,j) for i in e for j in g))
    # Deleting any two vertices leaves >=80 marks. Equality at degree<=8
    # requires 20 positive marked vertices, but at most one of 22 can die:
    # a zeroed vertex has old degree <=2, and k>=9 with sum deficit20.
    for i,j in pairs:
        f.clause(*(f.conjunction(hs[v][9],f.conjunction(-get(host,v,i),-get(host,v,j)))
                   for v in range(n) if v not in (i,j)))
    for clique in combinations(range(n),4):
        if sum(v<s for v in clique)<=2:
            f.clause(*(-mark[e] for e in combinations(clique,2)))

    triangles=[f.conjunction(mark[x,y],f.conjunction(mark[x,z],mark[y,z]))
               for x,y,z in combinations(range(n),3) if z>=s]
    if fixed is not None:
        f.at_most(triangles,(156-sum(d*(9-d) for d in fixed))//6)
    else:
        f.at_most(triangles,triangle_cap(k))
        if use_weight:
            terms=[(tri,3) for tri in triangles]
            for v in U:
                for d in range(1,9):
                    exact=f.conjunction(ds[v][d],-ds[v][d+1])
                    terms.append((exact,d*(9-d)//2))
            weight_cap(f,terms,78)

    if shape=="chain":
        left=[f.variable() for _ in A]
        f.clause(left[max(1,s-9)-1])
        f.clause(-left[s//2])
        for v in range(s-1):
            f.clause(-left[v+1],left[v])
        for i,j in combinations(A,2):
            f.clause(-mark[i,j],left[i])
            f.clause(-mark[i,j],-left[j])
            if i+1<j:
                f.clause(-mark[i+1,j],mark[i,j])
            if j+1<s:
                f.clause(left[j],-mark[i,j+1],mark[i,j])
    elif shape=="c5":
        part=[]
        for v in A:
            if v<5:
                part.append([yes if j==v else no for j in range(6)])
            else:
                bits=[f.variable() for _ in range(6)]
                part.append(bits)
                f.clause(*bits)
                f.at_most(bits,1)
        for i,j in combinations(A,2):
            for a in range(6):
                for b in range(6):
                    e=mark[i,j] if max(a,b)<5 and (a-b)%5 in (1,4) else -mark[i,j]
                    f.clause(-part[i][a],-part[j][b],e)
        for i in range(5,s-1):
            for a in range(6):
                for b in range(a):
                    f.clause(-part[i][a],-part[i+1][b])
    else:
        raise ValueError(shape)

    for i in range(s,n-1):
        j=i+1
        if fixed is None:
            for d in range(1,9):
                f.clause(-ds[j][d],ds[i][d])
        elif fixed[i-s]!=fixed[j-s]:
            continue
        # Within equal degree labels, choose lexicographic maximum.
        prefix=yes
        for d in range(1,9):
            prefix=f.conjunction(prefix,f.disjunction(-ds[i][d],ds[j][d]))
        for v in range(n):
            if v in (i,j):
                continue
            for table in (mark,host):
                a,b=get(table,i,v),get(table,j,v)
                if a==b:
                    continue
                f.clause(-prefix,a,-b)
                prefix=f.conjunction(prefix,-xor(f,a,b))
    return f


def compress(path):
    target=path.with_suffix(path.suffix+".gz")
    with path.open("rb") as src,target.open("wb") as dst:
        with gzip.GzipFile(filename="",fileobj=dst,mode="wb",compresslevel=3,mtime=0) as gz:
            shutil.copyfileobj(src,gz)
    path.unlink()


def run(args, case):
    name,k,shape,fixed=case
    resultfile=args.out/(name+".json")
    if resultfile.exists():
        old=json.loads(resultfile.read_text())
        if old.get("result")=="VERIFIED_UNSAT":
            return old
    if datetime.now(timezone.utc)>=args.deadline:
        return dict(name=name,result="DEADLINE")
    f=instance(k,shape,not args.relaxed,fixed)
    cnf=args.out/(name+".cnf")
    proof=args.out/(name+".lrat")
    f.dump(cnf)
    with (args.out/(name+".log")).open("wb") as log:
        timer=max(1,min(args.timeout,(args.deadline-datetime.now(timezone.utc)).total_seconds()))
        try:
            status=subprocess.run([str(args.solver),"--lrat","--no-binary",str(cnf),str(proof)],
                                  stdout=log,stderr=subprocess.STDOUT,timeout=timer).returncode
        except subprocess.TimeoutExpired:
            status=None
    result=dict(name=name,k=k,shape=shape,fixed=fixed,weighted=not args.relaxed,
                variables=f.variables,clauses=len(f.clauses),result="UNKNOWN",code=status)
    if status==20:
        replay=subprocess.run([str(args.checker),cnf.name,proof.name],cwd=args.out,
                              check=True,text=True,capture_output=True)
        result.update(result="VERIFIED_UNSAT",replay=json.loads(replay.stdout),
                      cnf_sha256=file_digest(cnf),lrat_sha256=file_digest(proof))
        for p in (cnf,proof):
            compress(p)
    elif status==10:
        result["result"]="SAT"
    else:
        cnf.unlink()
        if proof.exists():
            proof.unlink()
    resultfile.write_text(json.dumps(result)+"\n")
    print(result,flush=True)
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out",type=Path,required=True)
    parser.add_argument("--solver",type=Path,required=True)
    parser.add_argument("--checker",type=Path,required=True)
    parser.add_argument("--deadline",type=datetime.fromisoformat,required=True)
    parser.add_argument("--minimum",type=int,default=9)
    parser.add_argument("--maximum",type=int,default=18)
    parser.add_argument("--jobs",type=int,default=3)
    parser.add_argument("--timeout",type=int,default=180)
    parser.add_argument("--relaxed",action="store_true")
    parser.add_argument("--fixed",action="store_true")
    args=parser.parse_args()
    args.out.mkdir(parents=True,exist_ok=True)
    if args.fixed:
        from itertools import combinations_with_replacement
        cases=[
            (f"k{k}_{shape}_"+"".join(map(str,fixed)),k,shape,fixed)
            for k in reversed(range(args.minimum,args.maximum+1))
            for fixed in combinations_with_replacement(range(1,9),k)
            if sum(fixed)==20 and sum(d*d for d in fixed)>=24
            for shape in ("chain","c5")
        ]
    else:
        cases=[(f"k{k}_{shape}",k,shape,None)
               for k in reversed(range(args.minimum,args.maximum+1))
               for shape in ("chain","c5")]
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        results=list(pool.map(lambda case:run(args,case),cases))
    (args.out/"summary.json").write_text(json.dumps(results,indent=2)+"\n")


if __name__=="__main__":
    main()

