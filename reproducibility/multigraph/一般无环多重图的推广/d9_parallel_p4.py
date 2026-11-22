"""Integer residual tests for q=12, p=4."""

from collections import Counter
from fractions import Fraction
from functools import cache
from itertools import combinations, product

from d9_parallel_counts import local_ore_rows
from d9_parallel_p5 import splits


def check_degree_seven():
    for w in range(12,15):
        top=0
        for a,b,c,d in product(range(8),repeat=4):
            if a+b+c+d!=w or max(a+b,c+d,a+c,b+d)>7:
                continue
            types=(a,b,c,d)
            top=max(top,sum(x*min(7,9-y) for x,y in zip(types,reversed(types))))
        if top!=(74,75,76)[w-12]:
            raise ValueError((w,top))
        for bits in range(3,7):
            blanks=bits-2
            lower=14*bits*(w-7)-14*blanks
            upper=w*(w-1)+(bits-1)*(9*w-78)
            if lower<=upper:
                raise ValueError((w,bits,lower,upper))


def check_interior_maximum():
    active=[(r0,a,delta,f,pi,min(top,7*a)+f)
            for side,r0,a,delta,f,pi,top,_ in local_ore_rows(78,9,8)
            if side==0 and min(top,7*a)+f>=78]
    if not active or any(r0!=8 or a!=8 or delta>5 or f!=22 or pi<12 or total!=78
                         for r0,a,delta,f,pi,total in active):
        raise ValueError(active)


@cache
def witness_cost(t, columns, unmarked, a, degree):
    infinite=Fraction(10**6)
    needs=tuple(max(0,a-value) for value in t)
    best=sum((Fraction(need*copies,degree-need) if need<degree else infinite)
             for need,copies in zip(needs,columns) if copies)
    if not unmarked:
        return best
    for use in range(1,unmarked+1):
        for weights in product(*(range(min(3,value)+1) for value in columns)):
            if not any(weights):
                continue
            root_need=max(needs[i] for i,x in enumerate(weights) if x)
            marker_need=max(0,root_need-use)
            local=sum(weights)
            if local+root_need>9 or local+marker_need>degree:
                continue
            rem=tuple(y-x for x,y in zip(weights,columns))
            best=min(best,marker_need+witness_cost(t,rem,unmarked-use,a,degree))
    return best


@cache
def inside_profiles(t, maximum, unmarked, a):
    """Enumerate host multiplicities between F's A columns."""
    pairs=tuple(combinations(range(len(t)),2))
    outputs=[]

    def walk(index, remaining, loose, edges):
        if index==len(pairs):
            degrees=tuple(sum(m for u,v,m in edges if z in (u,v)) for z in range(len(t)))
            outputs.append((degrees,frozenset((u,v) for u,v,_ in edges),
                            sum(m for _,_,m in edges)))
            return
        u,v=pairs[index]
        walk(index+1,remaining,loose,edges)
        if t[u]+t[v]>=a:
            for m in range(1,min(3,remaining)+1):
                walk(index+1,remaining-m,loose,(*edges,(u,v,m)))
        elif remaining and loose:
            walk(index+1,remaining-1,loose-1,(*edges,(u,v,1)))

    walk(0,maximum,unmarked,())
    return tuple(outputs)


def active_profiles(degree):
    states=local_ore_rows(78,9,degree)
    if degree==8 and {row[1:3] for row in states if row[0]}!={(9,7),(9,8)}:
        raise ValueError("unlisted degree-eight exterior root")
    if degree==9 and {row[1:3] for row in states if row[0]}!={(9,9)}:
        raise ValueError("unlisted degree-nine exterior root")
    for k in (2,3):
        budget=6+k
        for r in range(12,19-2*k):
            for m in range(78,84 if degree==8 else 82):
                internal=102-k-r-m
                slack=budget-internal
                if min(slack,internal)<0:
                    continue
                for side,_,a,delta,f,pi,top,total in states:
                    if not side or total<m or pi>budget:
                        continue
                    for location in ((0,1) if degree==8 else (2,)):
                        # 0: C in W. 1: C in A. 2: C empty.
                        if location==1 and not slack:
                            continue
                        contribution_cap=min(8,15-a) if location==0 else (7 if location==1 else 0)
                        for contribution in range(max(0,m-f-top),contribution_cap+1):
                            yield k,r,m,internal,slack,delta,f,pi,a,location,contribution


def aggregate_options(profile, degree):
    k,r,m,internal,slack,delta,f,pi,a,location,c=profile
    c_a=int(location==1)
    width=12-a-c_a
    cross=m-f-c
    outside_degree=degree
    for i_u in range(slack//2+1):
        internal_host=internal+i_u
        outside_budget=slack-2*i_u-c_a
        for u_f in range(outside_budget+1):
            cross_inside=pi-u_f
            if not 0<=cross_inside<=internal_host:
                continue
            for t in splits(cross_inside,width):
                if any(t[j]>t[j+1] for j in range(width-1)):
                    continue
                for e,among,count in inside_profiles(t,internal_host-cross_inside,i_u,a):
                    max_extra=min(7-c,internal_host-cross_inside-count) if c_a else 0
                    for extra in (row for total in range(max_extra+1)
                                  for row in splits(total,width,0,3)):
                        for roots in (row for total in range(width,r-12+width+1)
                                      for row in splits(total,width,1,3)):
                            c_weights=splits(c,width,0,3) if location==0 else ((0,)*width,)
                            for to_c in c_weights:
                                if sum(max(0,x-1) for x in to_c)>3:
                                    continue
                                base=tuple(9-roots[j]-t[j]-e[j]-extra[j]-to_c[j]
                                           for j in range(width))
                                lost=sum(base)-f
                                if not 0<=lost<=outside_budget-u_f:
                                    continue
                                for loss in splits(lost,width):
                                    columns=tuple(x-y for x,y in zip(base,loss))
                                    if max(columns)>delta or min(columns)<0:
                                        continue
                                    yield t,columns,u_f,lost,cross-outside_degree,among,to_c


def run_incidence(degree):
    totals=Counter()
    retained=[]
    for profile in sorted(set(active_profiles(degree))):
        for data in set(aggregate_options(profile,degree)):
            t,columns,u_f,_,available,_,_=data
            totals[profile[0],profile[-2],profile[8]]+=1
            if witness_cost(t,columns,u_f,profile[8],degree)<=available:
                retained.append((profile,data))
    return totals,retained


@cache
def rows_possible(t, columns, u_f, u_local, available, among, to_c, a, degree, c_w):
    """Pack the residual marked W rows and charge their forced witnesses."""
    options=[]
    for weights in product(*(range(min(3,n)+1) for n in columns)):
        marks=frozenset(i for i,w in enumerate(weights) if w)
        if not marks or sum(max(0,w-1) for w in weights)>3:
            continue
        root_need=max(0,a-min(t[i] for i in marks))
        slack=9-root_need-sum(weights)
        if slack<0:
            continue
        for uf in range(u_f+1):
            h=max(0,root_need-uf)
            if h+sum(weights)>degree:
                continue
            for size in range(min(u_local,slack)+1):
                for others in combinations(set(range(len(t)))-marks,size):
                    host=marks|set(others)
                    c_required=(c_w>=0 and any(t[j]<h-c_w for j,w in enumerate(to_c)
                                                if w and j not in host))
                    if c_required and (not c_w or slack<=size):
                        continue
                    options.append((weights,marks,host,uf,size,int(c_required),
                                    slack-size-c_required,h))
    if not options:
        return False
    incompatible=[[False]*len(options) for _ in options]
    for i,j in combinations(range(len(options)),2):
        _,mi,hi,*_=options[i]
        _,mj,hj,*_=options[j]
        incompatible[i][j]=incompatible[j][i]=any(
            (min(x,y),max(x,y)) not in among for x in mi-hj for y in mj-hi
        )

    def place(rem, previous, first, used_f, used_local, used_c, charged):
        if not any(rem):
            return True
        if witness_cost(t,rem,u_f-used_f,a,degree)>available-charged:
            return False
        for index in range(first,len(options)):
            weights,_,_,uf,local,c,room,h=options[index]
            if (uf+used_f>u_f or local+used_local>u_local
                    or c+used_c>max(0,c_w) or charged+h>available):
                continue
            if any(x>y for x,y in zip(weights,rem)):
                continue
            witnesses=[j for j,(old,_) in enumerate(previous) if incompatible[index][old]]
            if len(witnesses)>room or any(previous[j][1]>=options[previous[j][0]][6]
                                         for j in witnesses):
                continue
            subset=tuple((old,count+(j in witnesses))
                         for j,(old,count) in enumerate(previous))
            subset+=((index,len(witnesses)),)
            if place(tuple(y-x for x,y in zip(weights,rem)),subset,index,uf+used_f,
                     local+used_local,c+used_c,charged+h):
                return True
        return False

    return place(columns,(),0,0,0,0,0)


if __name__ == "__main__":
    check_degree_seven()
    check_interior_maximum()
    print("Degree seven excluded",flush=True)
    for degree in (9,8):
        total,rows=run_incidence(degree)
        print(degree,sorted(total.items()),"surviving",len(rows),flush=True)
        print(Counter((p[0],p[2],p[8],p[9],p[10]) for p,_ in rows),flush=True)
        survivors=[]
        for profile,data in rows:
            if rows_possible(*data,profile[8],degree,
                             8-profile[10] if profile[9]==0 else -1):
                survivors.append((profile,data))
        print("residual row packings retained:",len(survivors),flush=True)
        expected=[((3,12,78,9,0,5,15,9,9,2,0),
                   ((3,3,3),(5,5,5),0,0,54,frozenset(),(0,0,0)))] if degree==9 else []
        if survivors!=expected:
            raise ValueError(survivors)
