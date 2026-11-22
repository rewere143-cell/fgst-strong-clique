"""Integer bounds for q=13, p=1 marked-spoke cores."""

from functools import cache
from itertools import product

from d9_q14_split_spokes import blocks, combined, detailed_rows, dirty_upper


def large_cores():
    remaining=[]
    for left,right in ((5,7),(6,6)):
        for x,y in product(range(3),repeat=2):
            if not 1<=x+y<=2:
                continue
            cut=x*(right-y)+y*(left-x)
            pieces=((left-x,right-y),)
            for u in range(1,21-cut):
                need=55-8*(x+y)+cut+u
                if dirty_upper(pieces,20-cut-u,u)>=need:
                    remaining.append((left,right,x,y,cut,u,need))
    if remaining!=[(5,7,1,1,10,7,56)]:
        raise ValueError(remaining)
    rows=[row for row in detailed_rows(4,6,3,7)
          if row[2]+row[3]==1 and row[0]+row[1]>=6]
    if rows!=[(3,5,1,0,3)]:
        raise ValueError(rows)
    return remaining,rows


def core_graphs(left,right,budget):
    cases=set()
    for a,b,z,t,e in detailed_rows(left,right,budget,1):
        if z+t!=1 or a+b<6:
            continue
        if not 0<=budget-e<=1:
            raise ValueError((a,b,z,t,e,budget))
        selected=frozenset((i,j) for i,j in product(range(left),range(right))
                           if (i<a and j>=b+t) or (j<b and i>=a+z))
        cases.add(selected)
        if budget>e:
            for edge in product(range(left),range(right)):
                if edge not in selected:
                    cases.add(selected|{edge})
    return sorted(cases,key=lambda edges:sorted(edges))


def check_columns(left,right,u,edges):
    full=(1<<(left+right))-1
    missed=[]
    caps=[]
    for i in range(left):
        adj=sum(1<<(left+j) for j in range(right) if (i,j) in edges)
        missed.append((full^((1<<left)-1))^adj)
        caps.append(8-adj.bit_count())
    for j in range(right):
        adj=sum(1<<i for i in range(left) if (i,j) in edges)
        missed.append(((1<<left)-1)^adj)
        caps.append(8-adj.bit_count())
    options={}
    need=55+u
    for marks in range(1,full+1):
        count=marks.bit_count()
        if count>8 or count+2+8*(u-1)<need:
            continue
        host=marks
        for i in range(left+right):
            if marks>>i&1:
                host|=missed[i]
        if (host^marks).bit_count()!=1:
            continue
        value=min(8,count+min(count,2))
        options[host]=max(options.get(host,0),value)
    rows=sorted(options.items())
    for col in range(left+right):
        f0=max((value for host,value in rows if not host>>col&1),default=0)
        f1=max((value for host,value in rows if host>>col&1),default=0)
        if max(i*f1+(u-i)*f0 for i in range(min(u,caps[col])+1))<need:
            return 0

    @cache
    def best(u,remaining,need,first):
        if need<=0:
            return True
        if need>8*u:
            return False
        blocked=sum(1<<i for i,r in enumerate(remaining) if not r)
        for j in range(first,len(rows)):
            host,value=rows[j]
            if host&blocked or value+8*(u-1)<need:
                continue
            next_caps=tuple(r-(host>>i&1) for i,r in enumerate(remaining))
            if best(u-1,next_caps,need-value,j):
                return True
        return False

    return None if best(u,tuple(caps),need,0) else 1


def connected_cores():
    profiles=[(l,r,u) for l,r in ((5,7),(6,6)) for u in range(1,21)
              if dirty_upper(((l,r),),20-u,u)>=55+u]
    if profiles!=[(5,7,8),(5,7,9),(6,6,8)]:
        raise ValueError(profiles)
    counts=[0,0,0]
    for left,right,u in profiles:
        for graph in core_graphs(left,right,20-u):
            excluded=check_columns(left,right,u,graph)
            counts[2 if excluded is None else excluded]+=1
    return counts


def small_cores():
    checked=0
    rest=[]
    for left,right in ((5,7),(6,6)):
        for pieces in blocks(left,right):
            cut=left*right-sum(a*b for a,b in pieces)
            for u in range(21-cut):
                checked+=1
                if combined(pieces,20-cut-u,u,base=55):
                    rest.append((left,right,pieces,cut,u))
    return checked,rest


if __name__=="__main__":
    print("Large proper core residual:",large_cores())
    counts=connected_cores()
    print("Connected core: one/all columns exclude, then unresolved:",counts)
    if counts!=[30,0,0]:
        raise ValueError(counts)
    checked,rest=small_cores()
    print("Small-core profiles checked and not excluded:",checked,len(rest))
    if checked!=175 or len(rest)!=42 or {sum(row[2][0]) for row in rest}!={8,9}:
        raise ValueError((checked,rest))
    print(*rest,sep="\n")
