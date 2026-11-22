"""Integer bounds for a disconnected q=14 fully marked spoke core."""

from functools import cache
from itertools import product


@cache
def blocks(left,right,head=()):
    if not left+right:
        return ((),)
    options=[]
    for x,y in product(range(left+1),range(right+1)):
        key=(x+y,x,y)
        if not 1<=x+y<=9 or (head and key>head):
            continue
        if x+y>1 and min(x,y)==0:
            continue
        for end in blocks(left-x,right-y,key):
            options.append(((x,y),*end))
    return tuple(options)


@cache
def rows_for_block(left,right,budget,unmarked):
    choices=set()
    for a,b,z,t in product(range(left+1),range(right+1),range(left+1),range(right+1)):
        if a+z>left or b+t>right:
            continue
        marks=a+b
        u=z+t
        if u>unmarked or marks+u>9:
            continue
        if marks and marks+u<left+right and (not u or u+budget<min(left,right)):
            continue
        edges=a*(right-b-t)+b*(left-a-z)
        if edges<=budget:
            choices.add((marks,u,edges))
    return tuple(choices)


def dirty_upper(pieces,budget,unmarked):
    values={0:0}
    options={(0,0,0)}
    for left,right in pieces:
        paired=set()
        for a,u,e in options:
            for b,v,f in rows_for_block(left,right,budget,unmarked):
                if u+v<=unmarked and a+b+u+v<=9 and e+f<=budget:
                    paired.add((a+b,u+v,e+f))
        options=paired
    for marks,u,_ in options:
        if marks and u:
            gain=min(9-u,marks+min(marks,2))
            values[u]=max(values.get(u,0),gain)
    best=[0]
    for u in range(1,unmarked+1):
        best.append(max((best[-1],*(gain+best[u-cost] for cost,gain in values.items()
                                    if 1<=cost<=u))))
    return best[-1]


@cache
def clean_upper(pieces,budget):
    rooms=tuple((1+min(x,y)) for x,y in pieces)
    sizes=tuple(x+y for x,y in pieces)
    rows=[]
    for mask in range(1,1<<len(sizes)):
        chosen=tuple(j for j in range(len(sizes)) if mask>>j&1)
        degree=sum(sizes[j] for j in chosen)
        if degree<=9:
            rows.append((mask,chosen,degree))
    if len(rows)>100:
        raise ValueError("the enumerated block partition is too fine")
    forced=[]
    for mask,_,_ in rows:
        forced.append(tuple(i for i,(other,_,_) in enumerate(rows)
                            if sum(x*x2+y*y2 for k,(x,y) in enumerate(pieces)
                                   if (mask&~other)>>k&1
                                   for j,(x2,y2) in enumerate(pieces)
                                   if (other&~mask)>>j&1)>budget))
    best=0
    counts=[0]*len(rows)

    def walk(i,caps,needs):
        nonlocal best
        if i==len(rows):
            value=sum(n*min(d+2,9-h) for n,h,(_,_,d) in zip(counts,needs,rows))
            best=max(best,value)
            return
        _,selected,degree=rows[i]
        maximum=min(caps[j] for j in selected)
        for n in range(maximum+1):
            if n and needs[i]+degree>9:
                break
            if n and any(counts[j] and needs[j]+n+rows[j][2]>9 for j in forced[i]):
                break
            counts[i]=n
            next_caps=tuple(c-(n if j in selected else 0) for j,c in enumerate(caps))
            next_needs=tuple(h+(n if j in forced[i] else 0) for j,h in enumerate(needs))
            walk(i+1,next_caps,next_needs)
        counts[i]=0

    walk(0,rooms,(0,)*len(rows))
    return best


def large_component():
    survivors=[]
    for x,y in product(range(5),repeat=2):
        if not 1<=x+y<=4:
            continue
        left,right=7-x,7-y
        cut=7*(x+y)-2*x*y
        for u in range(1,31-cut):
            budget=30-cut-u
            need=8*(left+right)-60+cut+u
            if dirty_upper(((left,right),),budget,u)>=need:
                survivors.append((left,right,cut,u,budget,need))
    if survivors!=[(5,5,20,6,4,46)]:
        raise ValueError(survivors)
    possibilities=[(a,b,z,t) for a,b,z,t in product(range(6),repeat=4)
                   if a+z<=5 and b+t<=5 and z+t==1 and 4<=a+b<=8
                   and a*(5-b-t)+b*(5-a-z)<=4]
    if possibilities!=[(4,4,0,1),(4,4,1,0)]:
        raise ValueError(possibilities)
    print("Large component checks, sole residual row bounds:",survivors,possibilities)


@cache
def detailed_rows(left,right,budget,unmarked):
    choices=[]
    for a,b,z,t in product(range(left+1),range(right+1),range(left+1),range(right+1)):
        if a+z>left or b+t>right or z+t>unmarked or a+b+z+t>9:
            continue
        edges=a*(right-b-t)+b*(left-a-z)
        if edges>budget or (a+b and a+b+z+t<left+right
                            and (not z+t or z+t+budget<min(left,right))):
            continue
        choices.append((a,b,z,t,edges))
    return tuple(choices)


def combined(pieces,budget,unmarked,base=52):
    """Return whether joint clean-dirty row incidence/capacity can reach M."""
    dirty=[]
    clean=[]
    for row in product(*(detailed_rows(a,b,budget,unmarked) for a,b in pieces)):
        marks=sum(a+b for a,b,_,_,_ in row)
        cost=sum(u+v for _,_,u,v,_ in row)
        edges=sum(e for *_,e in row)
        if not marks or marks+cost>9 or cost>unmarked or edges>budget:
            continue
        marked=tuple(d for a,b,*_ in row for d in (a,b))
        host=tuple(d for a,b,u,v,_ in row for d in (a+u,b+v))
        first=(cost,marks,marked,host,edges)
        (dirty if cost else clean).append(first)
    clean.sort(key=lambda row:(-row[1],row[2]))
    left=sum(a for a,_ in pieces)
    right=sum(b for _,b in pieces)
    slots=tuple(n*(8-total+m) for a,b in pieces for n,m,total in ((a,b,right),(b,a,left)))
    target=base+unmarked

    def force(first,second):
        _,_,a,b,e=first
        _,_,c,d,f=second
        total=0
        for j in range(2):
            total+=sum(max(a[i]-d[i],0) for i in range(j,len(a),2))*sum(
                max(c[i]-b[i],0) for i in range(j,len(a),2))
        return total+max(e,f)>budget

    clean_forced=[tuple(j for j,b in enumerate(clean) if force(a,b)) for a in clean]
    dirty_forced=[tuple(j for j,b in enumerate(clean) if force(a,b)) for a in dirty]

    def dirty_upper_given_clean(need,remaining,chosen,rooms):
        if need<=0:
            return True
        if need>8*unmarked:
            return False
        usable=[]
        for row,forbidden in zip(dirty,dirty_forced):
            u,d,_,host,_=row
            adjacent=sum(chosen[j] for j in forbidden)
            if d+u+adjacent>9 or any(h>r for h,r in zip(host,remaining)):
                continue
            if any(chosen[j] and rooms[j]==0 for j in forbidden):
                continue
            usable.append((u,min(d+min(2,d),9-u-adjacent),host,forbidden))
        if not usable:
            return False
        if sum(remaining)<need:
            return False
        # Relax separately to one degree column or one clean-row class.
        limits=[((),0)]
        limits.extend(((i,),r) for i,r in enumerate(remaining) if 0<r<unmarked*max(
            h[i] for _,_,h,_ in usable))
        limits.extend(((i+len(remaining),),r) for i,r in enumerate(rooms) if chosen[i] and 0<r<unmarked)
        for coords,cap in limits:
            options={}
            for u,f,h,adj in usable:
                c=(h[coords[0]] if coords[0]<len(remaining) else int(coords[0]-len(remaining) in adj)) if coords else 0
                options[u,c]=max(options.get((u,c),0),f)
            @cache
            def best(u,c):
                return max((f+best(u-a,c-b) for (a,b),f in options.items() if a<=u and b<=c),default=0)
            if best(unmarked,cap)<need:
                return False
        usable.sort(key=lambda row:(row[0],-row[1],row[2]))
        @cache
        def fill(first,u,r,h,need):
            if need<=0:
                return True
            if need>8*u or sum(r)<need:
                return False
            for j in range(first,len(usable)):
                cost,f,host,forbidden=usable[j]
                if cost>u or 8*(u-cost)+f<need or any(a>b for a,b in zip(host,r)):
                    continue
                if any(chosen[i] and h[i]==0 for i in forbidden):
                    continue
                next_r=tuple(b-a for a,b in zip(host,r))
                next_h=tuple(a-int(bool(chosen[i]) and i in forbidden) for i,a in enumerate(h))
                if fill(j,u-cost,next_r,next_h,max(0,need-f)):
                    return True
            return False
        return fill(0,unmarked,remaining,rooms,need)

    chosen=[0]*len(clean)

    def pack_clean(i,caps,touches):
        if i==len(clean):
            high=sum(n*min(d+2,9-h) for n,h,(_,d,*_) in zip(chosen,touches,clean))
            rooms=tuple(9-d-h for h,(_,d,*_) in zip(touches,clean))
            return dirty_upper_given_clean(target-high,caps,chosen,rooms)
        _,degree,_,host,_=clean[i]
        maximum=min(r//h for r,h in zip(caps,host) if h)
        for n in range(maximum+1):
            if n and degree+touches[i]>9:
                break
            if n and any(chosen[j] and touches[j]+clean[j][1]+n>9 for j in clean_forced[i]):
                break
            chosen[i]=n
            next_caps=tuple(r-n*h for r,h in zip(caps,host))
            next_touches=tuple(t+(n if j in clean_forced[i] else 0) for j,t in enumerate(touches))
            if pack_clean(i+1,next_caps,next_touches):
                return True
        chosen[i]=0
        return False

    return pack_clean(0,slots,(0,)*len(clean))


if __name__=="__main__":
    large_component()
    surviving=[]
    scanned=0
    for pieces in blocks(7,7):
        cut=49-sum(x*y for x,y in pieces)
        if cut>30:
            continue
        for unmarked in range(31-cut):
            scanned+=1
            budget=30-cut-unmarked
            clean=clean_upper(pieces,budget)
            dirty=dirty_upper(pieces,budget,unmarked)
            if clean+dirty>=52+unmarked:
                if combined(pieces,budget,unmarked):
                    surviving.append((pieces,cut,unmarked,clean,dirty))
    print(scanned,"component profiles checked")
    print(len(surviving),"with remaining capacity")
    if scanned!=174 or surviving:
        raise ValueError((scanned,surviving[:100]))
