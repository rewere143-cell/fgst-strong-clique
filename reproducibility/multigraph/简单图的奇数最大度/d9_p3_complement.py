"""Integer capacity relaxation for p=3 and an eight-point complement component."""

from functools import cache
from itertools import combinations_with_replacement, product


def orientations(k, left, right):
    for shape in combinations_with_replacement(range(3),3):
        shared=shape.count(2)
        if left+shape.count(0)+shared>9-k or right+shape.count(1)+shared>9-k:
            continue
        extras=6-2*k-shared
        if extras>=0:
            yield shape,extras


def specialty(orientation,left,right,x,y,budget):
    possibilities=[]
    for side in orientation:
        if side==0:
            possibilities.append(tuple(product(range(right+1),range(y+1))))
        elif side==1:
            possibilities.append(tuple(product(range(left+1),range(x+1))))
        else:
            possibilities.append(((0,0),))
    for adjacency in product(*possibilities):
        total=sum(sum(row) for row in adjacency)
        if total<=budget:
            yield adjacency,total


@cache
def partial_options(left,right,inner,unmarked):
    rows=[]
    for mx,my in product(range(left+1),range(right+1)):
        if not mx+my:
            continue
        hx,hy=left-mx,right-my
        for ux,uy in product(range(min(hx,unmarked)+1),range(min(hy,unmarked)+1)):
            use=ux+uy
            if not 1<=use<=unmarked or use+inner<min(left,right):
                continue
            rx,ry=hx-ux,hy-uy
            if not rx+ry or rx*my+ry*mx>inner:
                continue
            for fq in range(rx+ry,min(rx+ry+3,9-use)+1):
                rows.append((use,hx,hy,fq,rx+ry,mx,my))
    return tuple(rows)


def selected_types(options,shape,adjacency,core_other,selected):
    records={}
    for use,hx,hy,fq,mq,mx,my in options:
        allowed=[i for i in selected
                 if shape[i]==2 or (my if shape[i]==0 else mx)<=adjacency[i][0]]
        gain=0
        for pick in range(1,1<<len(allowed)):
            ids=[allowed[j] for j in range(len(allowed)) if (pick>>j)&1]
            need=max((max(0,core_other[1]-adjacency[i][1])
                      for i in ids if shape[i]==0),default=0)
            need+=max((max(0,core_other[0]-adjacency[i][1])
                       for i in ids if shape[i]==1),default=0)
            sc=min(len(ids)*3,len(ids)+3-(fq-mq),9-use-fq-need)
            if sc>=len(ids):
                gain=max(gain,sc)
        key=use,hx,hy,fq
        records[key]=max(records.get(key,0),gain)
    return tuple((*key,gain) for key,gain in records.items())


def mark_requirement(shape,adjacency,selected,extras,remaining):
    root=sum(2 if shape[i]==2 else 1 for i in selected)+extras
    spent=sum(sum(adjacency[i]) for i in selected)
    double_limit=3 if len(selected)==2 else 9
    return 9*len(selected)-root-spent-min(2*remaining,remaining+double_limit)


def test_one(k,left0,right0,x,y):
    left,right=left0-x,right0-y
    cut=x*right+y*left
    budget=7+k-cut
    if budget<0:
        return 0,[]
    surviving=[]
    scanned=0
    for shape,extras in orientations(k,left0,right0):
      for adjacency,d_special in specialty(shape,left,right,x,y,budget):
        dx=sum(adjacency[i][0] for i in range(3) if shape[i]==1)
        dy=sum(adjacency[i][0] for i in range(3) if shape[i]==0)
        for inner in range(budget-d_special+1):
          for unmarked in range(budget-d_special-inner+1):
            remaining=budget-d_special-inner-unmarked
            need=max(44+cut,64-extras-(7+k)-inner+d_special-dx-dy)
            cap_l=left*(8-y)-dx
            cap_r=right*(8-x)-dy
            total_cap=cap_l+cap_r-2*inner
            options=partial_options(left,right,inner,unmarked)
            for i in range(4):
                # i<3: only special i may have off-Q marks. i=3:
                # evaluate both no off-Q marks and at least two such specials.
                selected=tuple(j for j in range(3) if i!=j)
                need_special=mark_requirement(shape,adjacency,selected,extras,remaining)
                valuable=selected_types(options,shape,adjacency,(x,y),selected)

                @cache
                def solve(u,a,b,h,remainder):
                    best=0 if not remainder else -10**5
                    for cost,x1,y1,fq,gs in valuable:
                        if cost<=u and x1<=a and y1<=b and fq+cost<=h:
                            best=max(best,gs+solve(u-cost,a-x1,b-y1,h-fq-cost,
                                                    max(0,remainder-fq)))
                    return best

                for full in range(1,min(cap_l//left,cap_r//right)+1):
                    if total_cap<8*full:
                        continue
                    # Spend at least 8 full incidences, but allow their Q
                    # marks to give the optimistic 9 each for the target.
                    upper=solve(unmarked,cap_l-left*full,cap_r-right*full,
                                total_cap-8*full,max(0,need-9*full))
                    bonus=max(full,min(6,9-full)) if i==3 else 0
                    scanned+=1
                    if upper+bonus>=need_special:
                        surviving.append((shape,extras,adjacency,inner,unmarked,
                                          i,full,upper,need_special))
    return scanned,surviving


if __name__ == "__main__":
    total=0
    for k,left,right in ((2,2,7),(2,3,6),(2,4,5),(3,3,6),(3,4,5)):
        for x,y in ((0,1),(1,0)):
            scanned,rows=test_one(k,left,right,x,y)
            print((k,left,right,x,y),scanned,len(rows),rows[:3],flush=True)
            if rows:
                raise ValueError((k,left,right,x,y,rows[:3]))
            total+=scanned
    print("Excluded eight-point component capacity comparisons:",total)
