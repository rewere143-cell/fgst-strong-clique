"""Weighted degree-five flag model with simple projection and C5 abundance."""

import argparse
from fractions import Fraction as Q
from itertools import permutations
import json
from math import factorial, lcm
from pathlib import Path
import sys

from multigraph_lift_probe import decode, edge_pairs


def rooted_pentagon_rows(data,cycle,root):
    """Two pointwise pentagon upper bounds, summed over the first cycle vertex."""
    import numpy as np
    from scipy.sparse import csr_matrix

    orders = data["order"]
    untagged = data["mask"]==0
    support = [np.zeros(len(orders),dtype=np.int64) for _ in range(4)]
    paired_witnesses = np.zeros(len(orders),dtype=np.int64)
    for n in range(3,6):
        pairs = edge_pairs(n)
        for row in np.flatnonzero((orders==n)&untagged):
            colors = decode(n,int(data["code"][row]))
            lookup = {pair:color for pair,color in zip(pairs,colors)}

            def color(u,v):
                return lookup[min(u,v),max(u,v)]

            support[n-2][row] = factorial(n-1)*sum(
                all(color(v,u)==2 for u in range(n) if u!=v) for v in range(n)
            )
            if n!=5:
                continue
            for v,p,q,a,b in permutations(range(n)):
                if color(p,q)!=2 or color(v,p) or color(v,q):
                    continue
                if color(v,a)!=2 or color(v,b)!=2:
                    continue
                a_type = color(a,p),color(a,q)
                b_type = color(b,p),color(b,q)
                if a_type in ((0,2),(2,0)) and b_type in ((0,2),(2,0)):
                    paired_witnesses[row] += 1

    first,second,third = (csr_matrix(values) for values in support[1:])
    ore = Q(273323,10**6)
    return (
        ((1,cycle),(-Q(16,27)*ore,root)),
        ((1,cycle),(-ore/2,4*first-4*second+third)),
        ((1,cycle),(-Q(1,4),csr_matrix(paired_witnesses))),
    )


def enhanced_system(cache,settings):
    import numpy as np
    from scipy.sparse import csr_matrix, vstack
    from multigraph_weighted_maxdeg_exact import build_integer

    eq,ineq,grams,sizes,data,tags,scale,objective,roots = build_integer(cache,settings)
    norm = csr_matrix(data["normalizer"].astype(np.int64))
    plain_goal = csr_matrix((tags==0)*objective)
    root0 = csr_matrix(np.where((data["order"]==2)&(tags==0),2,0))
    c5 = []
    for row in np.flatnonzero((data["order"]==5)&(tags==0)):
        colors = decode(5,int(data["code"][row]))
        if colors.count(2)!=5 or 1 in colors:
            continue
        marked = [pair for pair,color in zip(edge_pairs(5),colors) if color==2]
        if all(sum(v in pair for pair in marked)==2 for v in range(5)):
            c5.append(int(row))
    assert len(c5)==1 and int(data["aut_count"][c5[0]])==10
    cycle = csr_matrix(([10],([0],c5)),shape=(1,len(objective)),dtype=np.int64)
    simple_cap = Q(settings["simple_support_cap"])
    gamma = Q(settings["abundance_gamma"])
    epsilon = Q(settings["abundance_epsilon"])
    mhi = Q(settings["mass_high"])
    assert simple_cap>=Q(5,4)-Q(167,10000) and mhi>=Q(1288281,1000000)
    assert 0<gamma<=Q(99999,100000) and epsilon>=Q(2,10**9)
    const = Q(5,4)-gamma/8+epsilon
    added = [
        ((Q(1,2),plain_goal),(-simple_cap,root0)),
        ((Q(1,2),plain_goal),(-gamma,cycle),(-const,root0)),
    ]
    if settings.get("rooted_pentagon"):
        added.extend(rooted_pentagon_rows(data,cycle,root0))
    if settings.get("forbid_pentagons"):
        all_cycle = (data["order"]==5)&(data["code"]==int(data["code"][c5[0]]))
        added.append(((Q(1),csr_matrix(all_cycle.astype(np.int64))),))
    elif settings.get("cycle_plain_cap") is not None:
        added.append(((Q(1),cycle),(-Q(settings["cycle_plain_cap"]),root0)))
    if settings.get("forbid_marked_triangles"):
        forbidden = np.zeros(len(objective),dtype=np.int64)
        for column in np.flatnonzero(data["order"]==3):
            colors = decode(3,int(data["code"][column]))
            forbidden[column] = int(all(colors) and 2 in colors)
        added.append(((Q(1),csr_matrix(forbidden)),))
    new_scale = lcm(scale,*(coefficient.denominator for row in added for coefficient,_ in row))
    multiplier = new_scale//scale
    ineq = vstack([ineq*multiplier,*(sum(int(coefficient*new_scale)*matrix
                                         for coefficient,matrix in row)
                                     for row in added)],format="csr")
    return (eq*multiplier,ineq,[matrix*multiplier for matrix in grams],sizes,
            data,tags,new_scale,objective,roots)


def solve(system,seconds,iterations,output,indirect=False,feasibility=False):
    import numpy as np
    from scipy.sparse import eye, vstack
    import scs

    eq,ineq,grams,sizes,data,tags,scale,objective,roots = system
    packed = []
    for matrix,size in zip(grams,sizes):
        rows,columns = np.tril_indices(size)
        order = np.lexsort((rows,columns))
        rows,columns = rows[order],columns[order]
        left = size*rows+columns
        right = size*columns+rows
        weights = np.where(rows==columns,1,np.sqrt(2))/(2*scale)
        packed.append(-((matrix[:,left]+matrix[:,right]).multiply(weights)).T)
    a = vstack((eq/scale,ineq/scale,-eye(len(objective)),*packed),format="csc")
    b = np.zeros(a.shape[0])
    b[0] = 1
    cone = dict(z=eq.shape[0],l=ineq.shape[0]+len(objective),s=sizes)
    c = np.zeros_like(objective,dtype=float) if feasibility else -objective/2
    opt = scs.SCS(dict(A=a,b=b,c=c),cone,
                  linear_solver="cpu_indirect" if indirect else "qdldl",
                  eps_abs=1e-7,eps_rel=1e-7,max_iters=iterations,
                  time_limit_secs=seconds,verbose=True)
    result = opt.solve()
    np.savez(output,**{key:result[key] for key in ("x","y","s")})
    print(json.dumps(result["info"],indent=2),flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("cache",type=Path)
    parser.add_argument("--vendor",type=Path)
    parser.add_argument("--lower",type=Q)
    parser.add_argument("--upper",type=Q)
    parser.add_argument("--seconds",type=int,default=200)
    parser.add_argument("--iterations",type=int,default=24000)
    parser.add_argument("--numerical",type=Path)
    parser.add_argument("--certificate",type=Path)
    parser.add_argument("--replay",action="store_true")
    parser.add_argument("--rooted-pentagon",action="store_true")
    parser.add_argument("--simple-cap",type=Q,default=Q(12378,10000))
    parser.add_argument("--mass-low",type=Q,default=Q(5,4))
    parser.add_argument("--mass-high",type=Q,default=Q(12895,10000))
    parser.add_argument("--local-beta",type=Q,default=Q(2987,10000))
    parser.add_argument("--ratio",action="store_true")
    parser.add_argument("--blend",action="store_true")
    parser.add_argument("--forbid-pentagons",action="store_true")
    parser.add_argument("--forbid-marked-triangles",action="store_true")
    parser.add_argument("--certificate-mode",choices=("infeasible","bound"),default="infeasible")
    parser.add_argument("--feasibility",action="store_true")
    parser.add_argument("--refit",action="store_true")
    args = parser.parse_args()
    if args.vendor:
        sys.path.insert(0,str(args.vendor))
    from multigraph_weighted_maxdeg_exact import rounded_certificate, verify
    if args.replay:
        cert = json.loads(args.certificate.read_text())
        system = enhanced_system(args.cache,cert["settings"])
        print(json.dumps(verify(args.cache,cert,system),indent=2))
        return
    settings = dict(e_low=str(args.lower),e_high=str(args.upper),mass_low=str(args.mass_low),
                    mass_high=str(args.mass_high),local_beta=str(args.local_beta),
                    simple_support_cap=str(args.simple_cap),abundance_gamma="99999/100000",
                    abundance_epsilon="1/500000000",rooted_pentagon=args.rooted_pentagon,
                    blend=args.blend,ratio=args.ratio,forbid_pentagons=args.forbid_pentagons,
                    forbid_marked_triangles=args.forbid_marked_triangles)
    system = enhanced_system(args.cache,settings)
    if args.certificate:
        result = rounded_certificate(args.cache,args.numerical,args.certificate_mode,settings,system)
        if args.refit:
            from multigraph_refit_exact_dual import repair

            result = repair(args.cache,result,args.seconds,system)
        replay = verify(args.cache,result,system)
        print(json.dumps(replay,indent=2))
        if replay["rigorous_infeasible"] or args.certificate_mode=="bound":
            args.certificate.write_text(json.dumps(result,separators=(",",":"))+"\n")
    else:
        solve(system,args.seconds,args.iterations,args.numerical,feasibility=args.feasibility)


if __name__=="__main__":
    main()
