"""Exact CNFs for the maximum-degree-eight parallel-mark branch."""

import argparse
from concurrent.futures import ThreadPoolExecutor
from functools import cache
import gzip
from hashlib import sha256
from itertools import combinations, product
import json
from pathlib import Path
import shutil
import subprocess
from time import monotonic, sleep

from d7_bipartite_ore_coupled import bound, local_bound
from d7_parallel_sat import GraphCNF, file_digest


def cases():
    # Distinct exclusive leaf tuples record marked multiplicity 0, 1, or 2.
    for left, right in product(range(7), repeat=2):
        if left <= right and left+right >= 5:
            yield (f'q12_l{left}_r{right}',
                   (1,)*left+(0,)*(6-left), (1,)*right+(0,)*(6-right), None)
    for left, right in product(range(6), range(7)):
        if left+right >= 8:
            yield (f'q11a_l{left}_r{right}',
                   (1,)*left+(0,)*(5-left), (1,)*right+(0,)*(6-right), None)
    for left, right in product(range(5), range(7)):
        if 2+left+right >= 9:
            yield (f'q11b_l{left}_r{right}',
                   (2,)+(1,)*left+(0,)*(4-left), (1,)*right+(0,)*(6-right), None)
    for left, right, x, y in product(range(6), range(6), range(2), range(2)):
        if (x,left) <= (y,right) and left+right+x+y >= 9:
            yield (f'q11c_l{left}{x}_r{right}{y}',
                   (1,)*left+(0,)*(5-left), (1,)*right+(0,)*(5-right), (x,y))


def partitions(total, maximum, length):
    if not total:
        yield ()
    elif length and total <= maximum*length:
        for n in range(1, min(total, maximum)+1):
            for rest in partitions(total-n, n, length-1):
                yield (n,)+rest


@cache
def exterior_limit(q, budget, cross_min):
    # A witness-group relaxation. If a group contains n chosen marked
    # exterior neighbors, its A-degree cannot exceed 7-n. Its degree units
    # earn n(n-2), with at most 2*budget units over all groups.
    for w in range(21, -1, -1):
        for groups in partitions(w, 7, q):
            earn = sorted(
                (n*(n-2) for n in groups if n > 2 for _ in range(7-n)),
                reverse=True,
            )
            group_cost = sum(n*n for n in groups)-sum(earn[:2*budget])
            if w*w+group_cost+cross_min <= 22*w:
                return w
    return 0


def instance(case, include_pairs=True, include_local=True, strict_q12=False, support_order=None):
    name, left, right, shared = case
    f = GraphCNF()
    yes, no = f.truth, -f.truth
    stop = 2 + len(left) + len(right) + int(shared is not None)
    A = range(2, stop)
    q = len(A)
    if strict_q12 and q != 12:
        raise ValueError('The strengthened encoding assumes q11 has been excluded.')
    spoke_marks = sum(left)+sum(right)+(sum(shared) if shared else 0)
    spoke_count = len(left)+len(right)+left.count(2)+(2 if shared else 0)
    p = spoke_count-spoke_marks
    budget = 8*q-79-p
    upper_cross = max(bound(7,8,15,D,q) for D in range(1,9))
    lower_cross = 79-spoke_marks-budget
    if not 0 <= lower_cross <= upper_cross:
        raise ValueError('Invalid root template')
    w_limit = exterior_limit(q,budget,lower_cross)
    if support_order is not None:
        if not strict_q12 or not stop < support_order <= stop+w_limit:
            raise ValueError('Support-order split outside the rooted bound')
        w_limit = support_order-stop
    n = stop+w_limit
    W = range(stop,n)

    root_records = {}
    group = [-1,-2]
    for root, values, start in ((0,left,2),(1,right,2+len(left))):
        for a, m in enumerate(values,start=start):
            root_records[root,a] = (yes, yes if m else no, yes if m==2 else no)
            group.append((root,m))
    if shared is not None:
        for i,m in enumerate(shared):
            root_records[i,stop-1] = (yes,yes if m else no,no)
        group.append((2,0))
    group.extend([(3,0)]*w_limit)

    edge,mark,double = {},{},{}
    possible_marked = []
    for u,v in combinations(range(n),2):
        if (u,v) == (0,1):
            e,m,d = yes,yes,yes
        elif u<2:
            e,m,d = root_records.get((u,v),(no,no,no))
        elif u in A:
            e,m,d = (f.variable() for _ in range(3))
            f.clause(-d,m)
            f.clause(-m,e)
        else:
            e,m,d = f.variable(),no,no
        edge[u,v],mark[u,v],double[u,v] = e,m,d
        if m!=no:
            possible_marked.append((u,v))

    def get(table,u,v):
        return table[min(u,v),max(u,v)] if u!=v else no

    deg,defect = [],[]
    for v in range(n):
        incidence = [get(table,v,u) for u in range(n) if u!=v for table in (edge,double)]
        seq = f.count(incidence,9)
        f.clause(-seq[9])
        deg.append(seq)
        if v in A:
            defect.extend(-seq[i] for i in range(1,9))
    for u,v in combinations(A,2):
        defect.extend((edge[u,v],double[u,v],f.conjunction(edge[u,v],-mark[u,v])))
    for u,v in product(A,W):
        defect.append(f.conjunction(edge[u,v],-mark[u,v]))
    f.at_most(defect,budget)

    for v in W:
        active = f.any(mark[u,v] for u in A)
        if support_order is not None:
            f.clause(active)
        for u in range(2,n):
            if u!=v:
                f.clause(-get(edge,v,u),active)
    for (a,b),(x,y) in combinations(possible_marked,2):
        if a in (x,y) or b in (x,y):
            continue
        f.clause(-mark[a,b],-mark[x,y],*(get(edge,i,j) for i in (a,b) for j in (x,y)))

    cross = [table[u,v] for u,v in product(A,W) for table in (mark,double)]
    cross_count = f.count(cross,upper_cross+1)
    f.clause(-cross_count[upper_cross+1])
    f.clause(cross_count[lower_cross])
    internal = [table[u,v] for u,v in combinations(A,2) for table in (mark,double)]
    internal_min = max(0,79-spoke_marks-upper_cross)
    f.clause(f.count(internal,internal_min)[internal_min])

    root_cost = {
        u:sum(get(table,i,u)==yes for i in range(2) for table in (edge,double))
        for u in A
    }
    cross_deg,distinct = {},{}
    for u in range(2,n):
        opposite = W if u in A else A
        cross_deg[u] = f.count([get(table,u,v) for v in opposite for table in (mark,double)],9)
        distinct[u] = f.count([get(mark,u,v) for v in opposite],9)
    cross_max = [f.any(cross_deg[u][i] for u in range(2,n)) for i in range(10)]
    for D in range(1,9):
        limit = bound(7,8,15,D,q)
        f.clause(-cross_max[D],cross_max[D+1],-cross_count[limit+1])
        if include_local:
            for u in range(2,n):
                side = int(u in W)
                fixed = root_cost.get(u,0)
                for host in range(D,9-fixed):
                    for a in range((D+1)//2,D+1):
                        local = local_bound(7,8,15,D,q,side,host,a)
                        if local < limit:
                            f.clause(cross_max[D+1],-cross_deg[u][D],
                                     -deg[u][host+fixed],deg[u][host+fixed+1],
                                     -distinct[u][a],distinct[u][a+1],
                                     -cross_count[local+1])
    low_ore_cap = max(bound(7,8,14,D,q) for D in range(1,9))
    ore_15 = [
        f.conjunction(mark[u,v],f.conjunction(deg[u][8],deg[v][8]))
        for u,v in product(A,W) if root_cost[u]==1
    ]
    for D in range(1,9):
        cap_d = bound(7,8,14,D,q)
        f.clause(-cross_max[D],cross_max[D+1],-cross_count[cap_d+1],*ore_15)
    f.clause(-cross_count[low_ore_cap+1],*ore_15)

    # Reuse the root-union lower bound on every repeated marked pair.
    for (u,v),d in double.items():
        if d==no:
            continue
        minimum = 8 if strict_q12 else 7
        f.clause(-d,deg[u][minimum])
        f.clause(-d,deg[v][minimum])
        f.clause(-d,deg[u][8],deg[v][8])
        losses = []
        for x in range(n):
            if x not in (u,v):
                losses.extend((
                    f.conjunction(get(edge,u,x),get(edge,v,x)),
                    get(double,u,x),get(double,v,x),
                ))
        if strict_q12:
            for loss in losses:
                f.clause(-d,-loss)
        else:
            for loss in losses:
                f.clause(-d,-loss,deg[u][8])
                f.clause(-d,-loss,deg[v][8])
            f.imply_at_most_one(d,losses)

    # If deleting two vertices left max degree 7, at most 16 marks would
    # be lost. Deleting both fixed roots and any exterior point costs
    # at most 22 marks, since the root bundle has multiplicity two.
    if include_pairs:
        for u,v in combinations(range(n),2):
            survivors = [
                f.conjunction(deg[x][8],f.conjunction(-get(edge,u,x),-get(edge,v,x)))
                for x in range(n) if x not in (u,v)
            ]
            f.clause(*survivors)
    for v in W:
        f.clause(*(f.conjunction(deg[x][8],-get(edge,v,x)) for x in W if x!=v))

    if strict_q12:
        # Choose the number of marked copies to be exactly 81. With every
        # double bundle in a matching, removing single marks always suffices.
        remaining_marks = cross+internal
        f.at_most(remaining_marks,79-spoke_marks)
        bundles = [d for d in double.values() if d!=no]
        f.clause(f.count(bundles,2)[2])
        # The root-pair-plus-one cut applies to both interior and exterior.
        for v in A:
            f.clause(*(f.conjunction(deg[x][8],-get(edge,v,x)) for x in W))
        # If an exterior witness is redundant, it can be deleted before
        # ordering the vertices. A necessary xy is the sole witness of
        # some two cross marks ax, by.
        for x,y in combinations(W,2):
            necessities = []
            for a,b in combinations(A,2):
                cross_x = f.conjunction(mark[a,x],-edge[a,y])
                cross_y = f.conjunction(mark[b,y],-edge[b,x])
                reverse_x = f.conjunction(mark[b,x],-edge[b,y])
                reverse_y = f.conjunction(mark[a,y],-edge[a,x])
                orientations = f.disjunction(f.conjunction(cross_x,cross_y),
                                             f.conjunction(reverse_x,reverse_y))
                necessities.append(f.conjunction(-edge[a,b],orientations))
            f.clause(-edge[x,y],*necessities)

    if support_order is not None:
        for u,v in possible_marked:
            union = [f.disjunction(get(edge,u,x),get(edge,v,x))
                     for x in range(n) if x not in (u,v)]
            f.clause(-mark[u,v],f.count(union,11)[11])
        if support_order >= 22:
            for a,b,c in combinations(range(n),3):
                f.clause(-mark[a,b],-mark[a,c],-mark[b,c])
        else:
            # The degree-eight case with 21 support points is the only
            # one in which a marked triangle could survive the count.
            incident_double = [f.any(get(double,u,v) for v in range(n) if u!=v)
                               for u in range(n)]
            for a,b,c in combinations(range(n),3):
                triangle_forbidden = (-mark[a,b],-mark[a,c],-mark[b,c])
                for v in (a,b,c):
                    f.clause(*triangle_forbidden,-incident_double[v])
                    f.clause(*triangle_forbidden,deg[v][8])

    for u in range(2,n-1):
        v = u+1
        if group[u]!=group[v]:
            continue
        prefix = yes
        for x in range(n):
            if x in (u,v):
                continue
            for table in (mark,double,edge):
                a,b = get(table,u,x),get(table,v,x)
                if a==b:
                    continue
                f.clause(-prefix,a,-b)
                if a==-b:
                    prefix=no
                else:
                    eq=f.disjunction(f.conjunction(a,b),f.conjunction(-a,-b))
                    prefix=f.conjunction(prefix,eq)
    return f,dict(name=name,q=q,p=p,budget=budget,w_limit=w_limit,lower_cross=lower_cross,
                  upper_cross=upper_cross,low_ore_cross=low_ore_cap,
                  mark=[(u,v,mark[u,v],double[u,v]) for u,v in possible_marked],
                  host=[(u,v,e,double[u,v]) for (u,v),e in edge.items() if e!=no])


def gzip_file(path):
    with path.open('rb') as source,path.with_suffix(path.suffix+'.gz').open('wb') as target:
        with gzip.GzipFile(filename='',fileobj=target,mode='wb',compresslevel=1,mtime=0) as stream:
            shutil.copyfileobj(source,stream)
    path.unlink()


def bounded_solve(solver, cnf, lrat, log, timeout, max_bytes):
    start = monotonic()
    with log.open('wb') as stream:
        proc = subprocess.Popen(
            [str(solver),'--lrat','--no-binary',str(cnf),str(lrat)],
            stdout=stream,stderr=subprocess.STDOUT,
        )
        try:
            while proc.poll() is None:
                if monotonic()-start>=timeout:
                    return None,'timeout'
                if lrat.exists() and lrat.stat().st_size>=max_bytes:
                    return None,'proof size limit'
                if shutil.disk_usage(lrat.parent).free<5*1024**3:
                    return None,'free space limit'
                sleep(.35)
            return proc.returncode,None
        finally:
            if proc.poll() is None:
                proc.kill()
                proc.wait()


def run_case(args,case):
    name=case[0]
    cnf=args.out/(name+'.cnf')
    proof=args.out/(name+'.lrat')
    result_file=args.out/(name+'.result.json')
    if result_file.exists():
        saved=json.loads(result_file.read_text())
        if saved['result']=='VERIFIED_UNSAT':
            return saved
    f,row=instance(case,not args.no_pairs,not args.no_local,args.strict_q12,args.support_order)
    f.dump(cnf)
    row.update(variables=f.variables,clauses=len(f.clauses),
               cnf_sha256=sha256(cnf.read_bytes()).hexdigest(),
               use_pairs=not args.no_pairs,use_local=not args.no_local,
               strict_q12=args.strict_q12,support_order=args.support_order)
    (args.out/(name+'.encoding.json')).write_text(json.dumps(row)+'\n')
    if not args.solver:
        print(name,row['variables'],row['clauses'],flush=True)
        return row
    log=args.out/(name+'.log')
    code,limit=bounded_solve(args.solver,cnf,proof,log,args.timeout,args.max_proof_mib*1024**2)
    result=dict(name=name,q=row['q'],p=row['p'],code=code,limit=limit,
                result='SAT' if code==10 else 'UNSAT' if code==20 else 'UNKNOWN')
    if code==20 and args.checker:
        replay=subprocess.run([str(args.checker),cnf.name,proof.name],cwd=args.out,
                              capture_output=True,text=True)
        result['replay_stdout']=replay.stdout
        result['replay_stderr']=replay.stderr
        if replay.returncode==0:
            result.update(result='VERIFIED_UNSAT',cnf_sha256=row['cnf_sha256'],lrat_sha256=file_digest(proof))
            if args.gzip:
                for path in (cnf,proof):
                    gzip_file(path)
        else:
            result['result']='CHECKER_FAILED'
    if result['result']=='UNKNOWN' and proof.exists():
        proof.unlink()
    result_file.write_text(json.dumps(result,indent=2)+'\n')
    print(name,result['result'],limit or '',flush=True)
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out',type=Path,required=True)
    parser.add_argument('--solver',type=Path)
    parser.add_argument('--checker',type=Path)
    parser.add_argument('--select',nargs='*')
    parser.add_argument('--family')
    parser.add_argument('--jobs',type=int,default=2)
    parser.add_argument('--timeout',type=int,default=120)
    parser.add_argument('--max-proof-mib',type=int,default=600)
    parser.add_argument('--gzip',action='store_true')
    parser.add_argument('--no-pairs',action='store_true')
    parser.add_argument('--no-local',action='store_true')
    parser.add_argument('--strict-q12',action='store_true')
    parser.add_argument('--support-order',type=int)
    parser.add_argument('--list',action='store_true')
    args=parser.parse_args()
    for key in ('solver','checker','out'):
        value=getattr(args,key)
        if value is not None:
            setattr(args,key,value.resolve())
    rows=list(cases())
    if args.family:
        rows=[case for case in rows if case[0].startswith(args.family)]
    if args.select:
        rows=[case for case in rows if case[0] in args.select]
    if args.support_order is not None:
        rows=[case for case in rows if case[0].startswith('q12') and
              21 <= args.support_order <=
              14+exterior_limit(12,5+sum(case[1])+sum(case[2]),
                                74-2*(sum(case[1])+sum(case[2])))]
        if args.support_order <= 22:
            rows=[case for case in rows
                  if 74-2*(sum(case[1])+sum(case[2])) <= 8*(args.support_order-14)]
    if args.list:
        print('\n'.join(case[0] for case in rows))
        return
    args.out.mkdir(parents=True,exist_ok=True)
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        result=list(pool.map(lambda case:run_case(args,case),rows))
    (args.out/'summary.json').write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':
    main()

