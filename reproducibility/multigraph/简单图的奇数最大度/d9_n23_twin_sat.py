"""Exact SAT instances for the D9 n23 saturated-triangle twin reduction."""
from concurrent.futures import ThreadPoolExecutor
from itertools import combinations, product
from pathlib import Path
import argparse
import json
import subprocess

from d7_bipartite_ore_coupled import bound, local_bound
from d7_parallel_sat import GraphCNF, file_digest


def instance(first_size, deficiency):
    X, Y, Z = range(6), range(6,12), range(12,19)
    groups = [0]*6+[1]*6+[2]*7
    labels = [
        (g, (i<first_size if g==0 else i-6<7-first_size) if g<2 else int(i==12))
        for i,g in enumerate(groups)
    ]
    f = GraphCNF()
    yes, no = f.truth, -f.truth
    edge, mark, unmark = {}, {}, {}
    markable = []
    for i,j in combinations(range(19),2):
        if j == 12:
            e = m = yes if ((i in X and i<first_size) or
                            (i in Y and i-6<7-first_size)) else no
        elif i == 12 and j in Z:
            e = m = no
        else:
            e = f.variable()
            m = f.variable() if groups[i]!=groups[j] else no
            f.clause(-m,e)
        edge[i,j],mark[i,j] = e,m
        if m != no:
            markable.append((i,j))
        unmark[i,j] = f.conjunction(e,-m)

    def get(tab,i,j):
        if i==j:
            return no
        return tab[min(i,j),max(i,j)]

    for i in range(19):
        f.at_most([get(edge,i,j) for j in range(19) if i!=j],7 if i in Z else 8)
    f.at_most(list(unmark.values()),5)
    wanted = 18+deficiency
    for literals, score in (
        ([mark[x,y] for x,y in product(X,Y)],wanted),
        ([mark[x,z] for x,z in product(range(12),Z)],49-deficiency),
    ):
        counts=f.count(literals,score+1)
        f.clause(counts[score])
        f.clause(-counts[score+1])

    for e,f_mark in combinations(markable,2):
        if len(set(e+f_mark))!=4:
            continue
        f.clause(-mark[e],-mark[f_mark],*(get(edge,i,j) for i,j in product(e,f_mark)))
    for i,j in markable:
        third = 3-groups[i]-groups[j]
        for z in (X,Y,Z)[third]:
            f.clause(-mark[i,j],get(edge,i,z),get(edge,j,z))

    # A cover of the unmarked graph with at most three points, including any
    # Z point, violates the linked-pair argument. Covers of size <=2 are
    # excluded by extending them to such a triple.
    for P in combinations(range(19),3):
        if max(P)>=12:
            f.clause(*(u for (i,j),u in unmark.items() if i not in P and j not in P))

    host_degree, marked_degree = {}, {}
    for i in range(12):
        host_degree[i]=f.count([get(edge,i,j) for j in range(12) if i!=j],9)
        opposite=Y if i in X else X
        marked_degree[i]=f.count([get(mark,i,j) for j in opposite],7)
    for x,y in product(X,Y):
        for d in range(2,9):
            f.clause(-mark[x,y],-host_degree[x][d],-host_degree[y][10-d])
    gd=[f.any(marked_degree[i][d] for i in range(12)) for d in range(8)]
    for d in range(1,7):
        if bound(8,8,9,d,6,1)<wanted:
            f.clause(-gd[d],gd[d+1])
            continue
        for side, group in enumerate((X,Y)):
            for host in range(d,9):
                if local_bound(8,8,9,d,6,side,host,d,1)<wanted:
                    for v in group:
                        f.clause(gd[d+1],-marked_degree[v][d],
                                 -host_degree[v][host],host_degree[v][host+1])

    # Global lexicographic maximum under permutations fixing the anchored
    # first Z vertex and its two prescribed adjacency sets.
    for i in range(18):
        j=i+1
        if labels[i]!=labels[j]:
            continue
        prefix=yes
        for z in range(19):
            if z in (i,j):
                continue
            for tab in (mark,edge):
                a,b=get(tab,i,z),get(tab,j,z)
                if a==b:
                    continue
                f.clause(-prefix,a,-b)
                same=f.disjunction(f.conjunction(a,b),f.conjunction(-a,-b))
                prefix=f.conjunction(prefix,same)
    return f


def run(args, case):
    p,d=case
    name=f"p{p}_d{d}"
    formula=instance(p,d)
    path=args.out/(name+".cnf")
    proof=args.out/(name+".lrat")
    formula.dump(path)
    result=dict(name=name,variables=formula.variables,clauses=len(formula.clauses),
                cnf_sha256=file_digest(path))
    if args.solver:
        with (args.out/(name+".log")).open("wb") as log:
            try:
                code=subprocess.run(
                    [str(args.solver),"--lrat","--no-binary",str(path),str(proof)],
                    stdout=log,stderr=subprocess.STDOUT,timeout=args.timeout
                ).returncode
            except subprocess.TimeoutExpired:
                code=None
        result["code"]=code
        if code==20 and args.checker:
            replay=subprocess.run([str(args.checker),path.name,proof.name],
                                  cwd=args.out,text=True,capture_output=True,check=True)
            result.update(replay=json.loads(replay.stdout),lrat_sha256=file_digest(proof))
    (args.out/(name+".json")).write_text(json.dumps(result)+"\n")
    print(result,flush=True)
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out",required=True,type=Path)
    parser.add_argument("--solver",type=Path)
    parser.add_argument("--checker",type=Path)
    parser.add_argument("--jobs",type=int,default=2)
    parser.add_argument("--timeout",type=int,default=120)
    args=parser.parse_args()
    args.out.mkdir(parents=True,exist_ok=True)
    cases=[(p,d) for d in range(1,5) for p in (2,3)]
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        rows=list(pool.map(lambda case:run(args,case),cases))
    (args.out/"summary.json").write_text(json.dumps(rows,indent=2)+"\n")


if __name__=="__main__":
    main()

