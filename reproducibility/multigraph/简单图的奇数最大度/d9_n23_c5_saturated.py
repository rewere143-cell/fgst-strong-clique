"""Exact d=9, m=98 search when saturated support is a C5 blowup."""
from itertools import combinations, combinations_with_replacement, product
from functools import reduce
from operator import and_
from collections import Counter
import argparse
import json


def cores(k,support=23):
    s=support-k
    outside_total=196-9*s
    for a in product(range(1,10),repeat=5):
        if sum(a)!=s:
            continue
        if a != min(b[i:]+b[:i] for b in (a,a[::-1]) for i in range(5)):
            continue
        slack=tuple(9-a[i-1]-a[(i+1)%5] for i in range(5))
        if any(v<0 or v>k or v>slack[(i+2)%5]+slack[(i+3)%5]
               for i,v in enumerate(slack)):
            continue
        cross=sum(x*y for x,y in zip(a,slack))
        if cross<=outside_total:
            yield a,slack,cross


def configurations(k,a,r,counts):
    full_options=[m for m in range(32) if sum(a[i] for i in range(5) if m>>i&1)<=8
                  and all(r[i] and (m>>((i+2)%5)&1 or m>>((i+3)%5)&1)
                          for i in range(5) if m>>i&1)]
    for kinds in combinations_with_replacement(full_options,k):
        full=[sum((kind>>i&1)<<x for x,kind in enumerate(kinds)) for i in range(5)]
        possible=[full[(i+2)%5]|full[(i+3)%5] for i in range(5)]
        if any(full[i].bit_count()>r[i] or possible[i].bit_count()<r[i]
               or full[i]&~possible[i]
               or (possible[i].bit_count()-r[i])*a[i] <
                  (possible[i]&~full[i]).bit_count()
               for i in range(5)):
            continue
        counts["full_patterns"] += 1
        families=[]
        for i in range(5):
            masks=[full[i]|sum(1<<x for x in seq) for seq in
                   combinations((x for x in range(k) if (possible[i]&~full[i])>>x&1),
                                r[i]-full[i].bit_count())]
            groups=[g for g in combinations_with_replacement(masks,a[i])
                    if reduce(and_,g)==full[i]]
            if not groups:
                break
            families.append(groups)
        if len(families)!=5:
            continue
        for all_groups in product(*families):
            masks=sum(all_groups,())
            deg=[sum(mask>>x&1 for mask in masks) for x in range(k)]
            if max(deg)>8:
                continue
            counts["cross_incidence_patterns"] += 1
            yield masks,deg


def check_completion(k,a,masks,degree,cross,counts):
    s=len(masks)
    n=s+k
    groups=sum((tuple([i]*size) for i,size in enumerate(a)),())
    base=set()
    for i,j in combinations(range(s),2):
        if (groups[i]-groups[j])%5 in (1,4):
            base.add((i,j))
    bridge={(i,s+x) for i in range(s) for x in range(k) if masks[i]>>x&1}
    fixed=base|bridge
    opts=set(combinations(range(s,n),2))

    def possible_witness(e,f):
        if len(set(e+f))<4:
            return None
        crosses={tuple(sorted((i,j))) for i in e for j in f}
        if crosses & fixed:
            return None
        return frozenset(crosses&opts)

    forced=set()
    for e,f in combinations(bridge,2):
        clause=possible_witness(e,f)
        if clause is not None:
            if not clause:
                return None
            if len(clause)!=1:
                raise AssertionError("two cross edges require only their outside join")
            forced.update(clause)

    eligible=[e for e in opts if all(possible_witness(e,f) is None for f in base)]
    need=(196-9*s-cross)//2
    for extra in combinations(eligible,need):
        hm=degree[:]
        for x,y in extra:
            hm[x-s]+=1;hm[y-s]+=1
        if min(hm)<1 or max(hm)>8:
            continue
        counts["outside_mark_patterns"] += 1
        host=forced|set(extra)
        spare=[9-h for h in degree]
        for x,y in host:
            spare[x-s]-=1;spare[y-s]-=1
        if min(spare)<0:
            continue
        clauses=[]
        for e,f in list(product(extra,bridge))+list(combinations(extra,2)):
            clause=possible_witness(e,f)
            if clause is not None and not clause&host:
                clauses.append(clause)

        def fill(remaining,space,used):
            if not remaining:
                return used
            best=min(remaining,key=lambda c: sum(space[x-s]>0 and space[y-s]>0 for x,y in c))
            for e in best:
                x,y=e
                if not (space[x-s]>0 and space[y-s]>0):
                    continue
                next_space=space[:]
                next_space[x-s]-=1; next_space[y-s]-=1
                answer=fill([c for c in remaining if e not in c],next_space,used|{e})
                if answer is not None:
                    return answer
            return None

        added=fill(clauses,spare,set())
        if added is not None:
            return dict(marked=sorted(fixed|set(extra)),host=sorted(fixed|host|added))
    return None


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--minimum",type=int,default=2)
    parser.add_argument("--maximum",type=int,default=6)
    parser.add_argument("--support",type=int,default=23)
    args=parser.parse_args()
    out=[]
    for k in range(args.minimum,args.maximum+1):
        counts=Counter()
        for a,slack,cross in cores(k,args.support):
            counts["cores"]+=1
            if (196-9*(args.support-k)-cross)%2:
                continue
            for masks,degree in configurations(k,a,slack,counts):
                witness=check_completion(k,a,masks,degree,cross,counts)
                if witness is not None:
                    print(json.dumps(dict(result="WITNESS",k=k,core=a,**witness)))
                    return
        out.append(dict(k=k,**counts))
    print(json.dumps(dict(result="NO_WITNESS",cases=out),indent=2))


if __name__=="__main__":
    main()

