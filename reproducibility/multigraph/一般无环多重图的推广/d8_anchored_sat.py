"""Exact degree-eight CNFs with a small-slack induced pentagon anchor."""

import argparse
from concurrent.futures import ThreadPoolExecutor
from itertools import combinations, product
import json
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

from d7_parallel_sat import GraphCNF, file_digest
from d7_verify_parallel import unpack
from d8_parallel_sat import bounded_solve, gzip_file


def slack_patterns(total):
    for prefix in product(range(total+1),repeat=4):
        last = total-sum(prefix)
        if last < 0:
            continue
        cycle = prefix + (last,)
        orbit = [v[i:]+v[:i] for v in (cycle,cycle[::-1]) for i in range(5)]
        if cycle != min(orbit):
            continue
        if any(4-total//2+cycle[(i+2)%5]+cycle[(i+3)%5] < 1 for i in range(5)):
            continue
        yield cycle


def add_anchor_swap_cuts(f,parts,core_order,n,edge,mark):
    """Choose an induced marked cycle with the largest possible exact core."""
    for vertex in range(5,core_order):
        anchors = list(range(5))
        anchors[parts[vertex]] = vertex
        eligible = []
        for u in range(n):
            types = []
            for i in range(5):
                intended = {(i-1)%5,(i+1)%5}
                z = f.truth
                for j,a in enumerate(anchors):
                    z = f.conjunction(z,mark(u,a) if j in intended else -edge(u,a))
                types.append(z)
            eligible.append(f.any(types))
        f.at_most(eligible,core_order)


def instance(slack,bundles,strengthened=False,anchor_swaps=False,*,extra_constraints=None):
    total = sum(slack)
    f = GraphCNF()
    yes,no = f.truth,-f.truth
    sizes = [4-total//2+slack[(i+2)%5]+slack[(i+3)%5] for i in range(5)]
    core_order = sum(sizes)
    outside = min(35-core_order,total+3*(total//3))
    n = core_order+outside
    parts = list(range(5))
    for i,size in enumerate(sizes):
        parts.extend([i]*(size-1))
    parts.extend([-1]*outside)
    pairs = tuple(combinations(range(n),2))
    edge,mark,double = {},{},{}
    for u,v in pairs:
        i,j = parts[u],parts[v]
        consecutive = i>=0 and j>=0 and (i-j)%5 in (1,4)
        if consecutive:
            e = yes
            m = yes if u<5 else f.variable()
            d = f.variable() if slack[i] and slack[j] else no
        elif (j>=0 and u<5) or (i>=0 and not slack[i]) or (j>=0 and not slack[j]):
            e=m=d=no
        else:
            e,m,d = (f.variable() for _ in range(3))
        f.clause(-d,m)
        f.clause(-m,e)
        edge[u,v],mark[u,v],double[u,v] = e,m,d

    def at(table,u,v):
        return table[min(u,v),max(u,v)] if u!=v else no

    if anchor_swaps:
        add_anchor_swap_cuts(f,parts,core_order,n,lambda u,v:at(edge,u,v),
                            lambda u,v:at(mark,u,v))

    host_degree = []
    active = [yes]*core_order
    for u in range(n):
        neighbors = [at(table,u,v) for v in range(n) if u!=v for table in (edge,double)]
        host_degree.append(f.count(neighbors,9))
        f.clause(-host_degree[u][9])
        if u>=core_order:
            active_u = f.any(at(mark,u,v) for v in range(n) if u!=v)
            active.append(active_u)
            for v in range(n):
                f.clause(-at(edge,u,v),active_u)
            for i in range(5):
                anchors = {(i-1)%5,(i+1)%5}
                f.clause(*(-at(mark,u,c) for c in sorted(anchors)),
                         *(at(edge,u,c) for c in range(5) if c not in anchors))
    active_count = f.count(active,22)
    f.clause(active_count[22 if strengthened else 21])

    mcount = f.count(list(mark.values())+list(double.values()),82)
    f.clause(mcount[81])
    f.clause(-mcount[82])
    dcount = f.count(list(double.values()),bundles+1)
    f.clause(dcount[bundles])
    f.clause(-dcount[bundles+1])

    marked_pairs = [pair for pair in pairs if mark[pair]!=no]
    for (a,b),(x,y) in combinations(marked_pairs,2):
        if a not in (x,y) and b not in (x,y):
            f.clause(-mark[a,b],-mark[x,y],
                     *(at(edge,u,v) for u in (a,b) for v in (x,y)))
    for a,b,c in combinations(range(n),3):
        if strengthened:
            f.clause(-mark[a,b],-mark[a,c],-mark[b,c])
        else:
            f.clause(-active_count[22],-mark[a,b],-mark[a,c],-mark[b,c])

    for u,v in marked_pairs:
        m,d = mark[u,v],double[u,v]
        union = [f.disjunction(at(edge,u,x),at(edge,v,x))
                 for x in range(n) if x not in (u,v)]
        f.clause(-m,f.count(union,11)[11])
        if d!=no:
            f.clause(-d,host_degree[u][8])
            f.clause(-d,host_degree[v][8])
            for x in range(n):
                if x in (u,v):
                    continue
                f.clause(-d,-at(double,u,x))
                f.clause(-d,-at(double,v,x))
                f.clause(-d,-at(edge,u,x),-at(edge,v,x))

    for u,v in pairs:
        if edge[u,v]==no:
            continue
        f.clause(*(f.conjunction(host_degree[x][8],
                                 f.conjunction(-at(edge,u,x),-at(edge,v,x)))
                   for x in range(n) if x not in (u,v)))

    for u in range(5,n-1):
        v = u+1
        if parts[u]!=parts[v]:
            continue
        previous = yes
        for x in range(n):
            if x in (u,v):
                continue
            for table in (mark,double,edge):
                a,b = at(table,u,x),at(table,v,x)
                if a!=b:
                    f.clause(-previous,a,-b)
                    eq = f.disjunction(f.conjunction(a,b),f.conjunction(-a,-b))
                    previous = f.conjunction(previous,eq)
    if extra_constraints is not None:
        extra_constraints(f, slack, parts, core_order, edge, mark, double)
    return f


def run(args,slack):
    name = 's' + ''.join(map(str,slack))
    cnf,proof,log,result = (args.out/(name+suffix)
                            for suffix in ('.cnf','.lrat','.log','.result.json'))
    if result.exists():
        saved = json.loads(result.read_text())
        if saved['result']=='VERIFIED_UNSAT':
            return saved
    instance(slack,args.bundles,args.strengthened,args.anchor_swaps).dump(cnf)
    code,limit = bounded_solve(args.solver,cnf,proof,log,args.timeout,
                               args.max_proof_mib*1024**2)
    row = dict(name=name,slack=slack,bundles=args.bundles,strengthened=args.strengthened,
               anchor_swaps=args.anchor_swaps,
               result='SAT' if code==10 else 'UNKNOWN',limit=limit)
    if code==20:
        check = subprocess.run([str(args.checker),cnf.name,proof.name],cwd=args.out,
                               capture_output=True,text=True,check=True)
        row.update(result='VERIFIED_UNSAT',replay=json.loads(check.stdout),
                   cnf_sha256=file_digest(cnf),lrat_sha256=file_digest(proof))
        gzip_file(cnf)
        gzip_file(proof)
    elif code!=10 and proof.exists():
        proof.unlink()
    result.write_text(json.dumps(row,indent=2)+'\n')
    print(name,row['result'],limit or '',flush=True)
    return row


def replay(args,slack):
    name = 's' + ''.join(map(str,slack))
    row = json.loads((args.out/(name+'.result.json')).read_text())
    if row.get('result')!='VERIFIED_UNSAT' or row['bundles']!=args.bundles:
        raise ValueError(f'{name}: no fixed proof for this bundle count')
    with TemporaryDirectory(prefix='fgst_d8_anchor_',dir=args.scratch) as directory:
        scratch = Path(directory)
        cnf,regenerated,proof = (scratch/file for file in ('archived.cnf','new.cnf','fixed.lrat'))
        instance(slack,args.bundles,row.get('strengthened',False),
                 row.get('anchor_swaps',False)).dump(regenerated)
        for target, suffix, key in ((cnf,'.cnf.gz','cnf_sha256'),
                                    (proof,'.lrat.gz','lrat_sha256')):
            if unpack(args.out/(name+suffix),target)!=row[key]:
                raise ValueError(f'{name}: archived {suffix} digest differs')
        if file_digest(regenerated)!=row['cnf_sha256']:
            raise ValueError(f'{name}: regenerated CNF differs')
        checked = subprocess.run([str(args.checker),cnf.name,proof.name],
                                 cwd=scratch,capture_output=True,text=True,check=True)
    row['replay'] = json.loads(checked.stdout)
    if row['replay'].get('added',0)<=0:
        raise ValueError(f'{name}: missing RUP replay count')
    print(name,row['replay']['added'],'verified RUP additions',flush=True)
    return row


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out',required=True,type=Path)
    parser.add_argument('--solver',type=Path)
    parser.add_argument('--checker',type=Path,default=Path('d7_rup_replay.exe'))
    parser.add_argument('--bundles',type=int,default=3)
    parser.add_argument('--slack',nargs='+',type=int,default=[4,6])
    parser.add_argument('--select',nargs='*')
    parser.add_argument('--jobs',type=int,default=5)
    parser.add_argument('--timeout',type=int,default=120)
    parser.add_argument('--max-proof-mib',type=int,default=350)
    parser.add_argument('--strengthened',action='store_true')
    parser.add_argument('--anchor-swaps',action='store_true')
    parser.add_argument('--verify',action='store_true')
    parser.add_argument('--scratch',type=Path,default=Path('.'))
    parser.add_argument('--report',type=Path)
    args = parser.parse_args()
    args.out,args.checker,args.scratch = (path.resolve()
                                          for path in (args.out,args.checker,args.scratch))
    if not args.verify:
        if not args.solver:
            parser.error('--solver is needed unless --verify is selected')
        args.solver = args.solver.resolve()
    args.out.mkdir(parents=True,exist_ok=True)
    cases = [case for total in args.slack for case in slack_patterns(total)]
    if args.select:
        cases = [case for case in cases if ''.join(map(str,case)) in args.select]
    action = replay if args.verify else run
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        results = list(pool.map(lambda row:action(args,row),cases))
    if args.verify:
        summary = dict(verified=True,bundles=args.bundles,cases=len(results),
                       additions=sum(row['replay']['added'] for row in results),
                       instances=results)
        if args.report:
            args.report.write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8')
        print(f"Verified {summary['cases']} formulas and {summary['additions']} RUP additions.",
              flush=True)
    else:
        (args.out/'summary.json').write_text(json.dumps(results,indent=2)+'\n')


if __name__=='__main__':
    main()
