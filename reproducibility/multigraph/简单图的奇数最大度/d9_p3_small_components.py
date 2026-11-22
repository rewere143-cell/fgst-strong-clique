"""Necessary integer capacity tests for p=3 and a smaller complement component."""

from functools import cache
from itertools import product

from d9_p3_complement import (mark_requirement, orientations, partial_options,
                              selected_types, specialty)


def shapes():
    for k,left,right in ((2,2,7),(2,3,6),(2,4,5),(3,3,6),(3,4,5)):
        for x,y in product(range(left),range(right)):
            g=9-x-y
            cut=x*(right-y)+y*(left-x)
            if 4<=g<=7 and cut<=7+k:
                yield k,left,right,x,y


@cache
def full_options(left,right,unmarked):
    result=[]
    g=left+right
    for u in range(min(g-1,unmarked)+1):
        for fq in range(g-u,min(g-u+3,9-u)+1):
            result.append((u,left,right,fq,g-u,0,0))
    return tuple(result)


def off_options(left,right,other,shape,adjacency,chosen,unmarked):
    result=set()
    for pick in range(1,1<<len(chosen)):
        selected=[chosen[j] for j in range(len(chosen)) if (pick>>j)&1]
        left_needs=[i for i in selected if shape[i]==1]
        right_needs=[i for i in selected if shape[i]==0]
        qx=max((left-adjacency[i][0] for i in left_needs),default=0)
        qy=max((right-adjacency[i][0] for i in right_needs),default=0)
        px=max((other[0]-adjacency[i][1] for i in left_needs),default=0)
        py=max((other[1]-adjacency[i][1] for i in right_needs),default=0)
        u=qx+qy
        gain=min(3*len(selected),len(selected)+3,9-u-px-py)
        if 1<=u<=unmarked and gain>=len(selected):
            result.add((u,qx,qy,0,gain))
    return tuple(sorted(result))


def test_one(k,left0,right0,x,y):
    left,right=left0-x,right0-y
    g=left+right
    cut=x*right+y*left
    budget=7+k-cut
    retained=[]
    tested=0
    for shape,extras in orientations(k,left0,right0):
      for adjacent,d_special in specialty(shape,left,right,x,y,budget):
        dx=sum(adjacent[i][0] for i in range(3) if shape[i]==1)
        dy=sum(adjacent[i][0] for i in range(3) if shape[i]==0)
        chosen=tuple(i for i in range(3) if shape[i]!=2 and
                     adjacent[i][0]<(right if shape[i]==0 else left))
        for inner in range(budget-d_special+1):
          for unmarked in range(budget-d_special-inner+1):
            remaining=budget-d_special-inner-unmarked
            need=max(76-8*(12-g)+cut,8*g-extras-(7+k)-inner+d_special-dx-dy)
            need_special=mark_requirement(shape,adjacent,chosen,extras,remaining)
            if not chosen:
                retained.append((shape,adjacent,inner,unmarked,'no paying special'))
                continue
            options=partial_options(left,right,inner,unmarked)
            # partial_options encodes g=8, so filter any host-complete rows.
            options=tuple(row for row in options if row[1]+row[2]<g)
            rest=selected_types(options,shape,adjacent,(x,y),chosen)
            rest+=off_options(left,right,(x,y),shape,adjacent,chosen,unmarked)
            full=selected_types(full_options(left,right,unmarked),shape,adjacent,(x,y),chosen)
            cap_l=left*(8-y)-dx
            cap_r=right*(8-x)-dy
            total_cap=cap_l+cap_r-2*inner

            @cache
            def best(b,u,h_l,h_r,h,s):
                outcomes=[]
                if not b and not s:
                    outcomes.append(0)
                for choices,drop in ((full,1),(rest,0)):
                    if drop>b:
                        continue
                    for cost,a,c,fq,gain in choices:
                        if cost<=u and a<=h_l and c<=h_r and fq+cost<=h:
                            outcomes.append(gain+best(b-drop,u-cost,h_l-a,h_r-c,
                                                      h-fq-cost,max(0,s-fq)))
                return max(outcomes,default=-10**5)

            for full_count in range(1,min(cap_l//left,cap_r//right)+1):
                tested+=1
                value=best(full_count,unmarked,cap_l,cap_r,total_cap,need)
                if value>=need_special:
                    retained.append((shape,adjacent,inner,unmarked,full_count,value,need_special))
    return tested,retained


if __name__ == "__main__":
    comparisons=profiles=0
    for shape in shapes():
        k,left,right,x,y=shape
        g=9-x-y
        cut=x*(right-y)+y*(left-x)
        if 76-8*(12-g)+cut<=8*(7+k-cut) and shape!=(2,2,7,0,2):
            raise ValueError(("unlisted complete-row exception",shape))
        total,kept=test_one(*shape)
        print(shape,total,len(kept),flush=True)
        comparisons+=total
        profiles+=len(kept)
        for row in kept:
            if len(row)!=7:
                raise ValueError((shape,row))
            kinds,adjacency,inner,unmarked,full_count,_,_=row
            if (shape not in ((2,3,6,1,1),(2,4,5,1,1))
                    or kinds.count(2) not in (1,2)
                    or inner+unmarked>1 or full_count>7):
                raise ValueError((shape,kinds,adjacency,inner,unmarked,full_count))
            left,right=shape[1]-shape[3],shape[2]-shape[4]
            if any((right if side==0 else left)-adjacency[i][0]<=unmarked
                   for i,side in enumerate(kinds) if side!=2):
                raise ValueError(("an exclusive special may have an off-component edge",
                                  shape,kinds,adjacency,unmarked))
    print("Smaller component capacity comparisons:",comparisons)
    print("Residual profiles covered by the two-slot argument:",profiles)
