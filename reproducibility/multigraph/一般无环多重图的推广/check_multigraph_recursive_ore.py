"""Certified recursive conditional estimates for bipartite marked strong cliques."""

import argparse
from fractions import Fraction as Q
import json
from pathlib import Path

from check_multigraph_bipartite_coupled import one_level_table, rectangle_score
from check_multigraph_bipartite_twolevel import base_upper, max_score


def max_child(table,a0,a1):
    bins = len(table)
    start = min(bins-1,int(a0*bins))
    end = min(bins-1,int(a1*bins))
    return max(table[start:end+1])


def certify_box(parent, a_interval, cap, work_limit=100000, depth_limit=56):
    """Prove a conditional bound on a single interval of root degrees."""
    if base_upper(*a_interval)>cap:
        return False,0,0
    pending = [(a_interval,(Q(0),Q(1)),(Q(0),Q(1)),0)]
    work = 0
    largest_depth = 0
    while pending:
        a,th,mu,depth = pending.pop()
        largest_depth = max(largest_depth,depth)
        a0,a1 = a
        t0,t1 = th
        u0,u1 = mu
        if t1+u1<=1 or a0*(t0+u0)>1:
            continue
        base = base_upper(a0,a1)
        p0,p1 = a0*t0,a1*t1
        tcap = p1*min(a1,1-a0)
        if base+tcap<=cap:
            continue
        tau_low,tau_hi = 1-p1,1-p0
        low = a0*u0/tau_hi if tau_hi else Q(0)
        high = a1*u1/tau_low if tau_low else Q(1)
        fcap = min(max_child(parent,low,high)*tau_hi**2,a1*u1*(1-a0))
        if base+max_score(fcap,t1,tcap)<=cap:
            continue
        if base+rectangle_score(tcap,fcap,t1,u1)<=cap:
            continue
        work += 1
        if work>work_limit or depth>=depth_limit:
            return False,work,largest_depth
        intervals = [a,th,mu]
        axis = max(range(3),key=lambda i:intervals[i][1]-intervals[i][0])
        left,right = intervals[axis]
        middle = (left+right)/2
        for subinterval in ((left,middle),(middle,right)):
            copy = intervals.copy()
            copy[axis] = subinterval
            pending.append((*copy,depth+1))
    return True,work,largest_depth


def refine(parent,candidates,limit):
    bins = len(candidates)
    output = []
    checked = skipped = work = depth = 0
    for i,cap in enumerate(candidates):
        a0,a1 = Q(i,bins),Q(i+1,bins)
        fallback = max_child(parent,a0,a1)
        if cap>=fallback:
            output.append(fallback)
            continue
        result,count,local_depth = certify_box(parent,(a0,a1),cap,work_limit=limit)
        if result:
            checked += 1
        else:
            skipped += 1
        output.append(cap if result else fallback)
        work += count
        depth = max(depth,local_depth)
    return output,dict(checked=checked,unproved_fallbacks=skipped,divisions=work,max_depth=depth)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--beta',type=Q,default=Q(2989,10000))
    parser.add_argument('--initial-bins',type=int,default=512)
    parser.add_argument('--suggestions',required=True,type=Path)
    parser.add_argument('--target',type=Q,required=True)
    parser.add_argument('--limit',type=int,default=3000)
    parser.add_argument('--report',type=Path)
    args = parser.parse_args()
    table = one_level_table(args.beta,args.initial_bins)
    report = {'initial_beta':str(args.beta),'initial_bins':args.initial_bins,'layers':[]}
    for estimates in json.loads(args.suggestions.read_text())['estimates']:
        table,stats = refine(table,[Q(item) for item in estimates],args.limit)
        report['layers'].append(stats)
        print(stats,flush=True)
    checked,count,depth = certify_box(table,(Q(0),Q(1)),args.target,work_limit=600000)
    report.update(target=str(args.target),proved=checked,divisions=count,max_depth=depth,
                  last_table=[str(value) for value in table])
    if args.report:
        args.report.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print({key:report[key] for key in ('target','proved','divisions','max_depth')},flush=True)
    if not checked:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
