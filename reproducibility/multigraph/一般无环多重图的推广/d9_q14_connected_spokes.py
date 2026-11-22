"""Column-capacity certificate for a connected q=14 fully marked spoke core."""

from functools import cache
from itertools import combinations, product


def first_rows(unmarked):
    for a,b,u,v in product(range(8),repeat=4):
        cost=u+v
        if not (a+b and 1<=cost<=unmarked and a+b+cost<=9 and a+u<=7 and b+v<=7):
            continue
        if (a,u)>(b,v):
            continue
        gain=min(9-cost,a+b+min(2,a+b))
        if unmarked*gain<(52+unmarked)*cost:
            continue
        touched=a*(7-b-v)+b*(7-a-u)
        if touched<=30-unmarked:
            yield a,b,u,v,30-unmarked-touched


def graphs(a,b,u,v,remaining):
    compulsory=[0]*7
    for i,j in product(range(7),repeat=2):
        if (i<a and j>=b+v) or (j<b and i>=a+u):
            compulsory[i]|=1<<j
    labels_left=tuple(0 if i<a else 1 if i<a+u else 2 for i in range(7))
    labels_right=tuple(0 if j<b else 1 if j<b+v else 2 for j in range(7))

    def add(rows,left,right,edges):
        yield tuple(rows)
        if not edges:
            return
        representative={}
        for i,j in product(range(7),repeat=2):
            if not rows[i]>>j&1:
                representative.setdefault((left[i],right[j]),(i,j))
        for i,j in representative.values():
            changed=list(rows)
            changed[i]|=1<<j
            next_left=tuple(max(left)+1 if z==i else label for z,label in enumerate(left))
            next_right=tuple(max(right)+1 if z==j else label for z,label in enumerate(right))
            yield from add(changed,next_left,next_right,edges-1)

    if remaining>2:
        raise ValueError(("first row leaves too many edges",a,b,u,v,remaining))
    return add(compulsory,labels_left,labels_right,remaining)


def column_options(left,unmarked):
    right=tuple(sum(1<<i for i,mask in enumerate(left) if mask>>j&1) for j in range(7))
    missing=tuple(127^mask for mask in (*left,*right))
    # allowed_l, allowed_r are the intersections of all A neighborhoods
    # of the marked endpoints on one side.
    def step(offset):
        intersections=[127]*128
        for mask in range(1,128):
            low=mask&-mask
            intersections[mask]=intersections[mask^low] & (127^missing[offset+low.bit_length()-1])
        return intersections
    near_l,near_r=step(0),step(7)
    possible={}
    for a,b in product(range(128),repeat=2):
        total=a.bit_count()+b.bit_count()
        if not 1<=total<=9:
            continue
        host_l=a | (127^near_r[b])
        host_r=b | (127^near_l[a])
        u=host_l.bit_count()+host_r.bit_count()-total
        if not 0<=u<=unmarked or total+u>9:
            continue
        # Zero cost would contradict connectivity of the 14-point
        # complement; omit it even in an over-inclusive graph template.
        if not u:
            continue
        host=host_l | (host_r<<7)
        gain=min(9-u,total+min(2,total))
        possible[u,host]=max(possible.get((u,host),0),gain)
    return tuple((u,host,gain) for (u,host),gain in possible.items()), \
        tuple(8-mask.bit_count() for mask in (*left,*right))


def limited(options,unmarked,choose):
    a,b=choose
    bit_a,bit_b=(1<<a[0] if a else 0),(1<<b[0] if b else 0)
    top_a,top_b=(a[1] if a else 0),(b[1] if b else 0)
    rows={}
    for u,mask,gain in options:
        key=u,int(bool(mask&bit_a)),int(bool(mask&bit_b))
        rows[key]=max(rows.get(key,0),gain)
    actual=tuple((*key,gain) for key,gain in rows.items())

    @cache
    def best(u,x,y):
        return max((gain+best(u-cost,x-i,y-j)
                    for cost,i,j,gain in actual if cost<=u and i<=x and j<=y),default=0)

    return best(unmarked,top_a,top_b)


def verify_one(left,unmarked):
    options,caps=column_options(left,unmarked)
    target=52+unmarked
    if limited(options,unmarked,(None,None))<target:
        return 0
    columns=sorted(enumerate(caps),key=lambda row:row[1])
    for entry in columns:
        if limited(options,unmarked,(entry,None))<target:
            return 1
    for pair in combinations(columns,2):
        if limited(options,unmarked,pair)<target:
            return 2
    if not packed(options,caps,unmarked,target):
        return 3
    if not copy_pack(left,caps,unmarked,target):
        return 4
    return None


def packed(options,caps,unmarked,target):
    rows=sorted(options,key=lambda row:(row[0],-row[2],row[1]))
    bare=[0]*(unmarked+1)
    for u in range(1,unmarked+1):
        bare[u]=max((gain+bare[u-cost] for cost,_,gain in rows if cost<=u),default=0)

    @cache
    def search(u,remaining,need,first):
        if need<=0:
            return True
        if bare[u]<need:
            return False
        zero=sum(1<<i for i,c in enumerate(remaining) if not c)
        for j in range(first,len(rows)):
            cost,host,gain=rows[j]
            if cost>u or bare[u-cost]<need-gain or host&zero:
                continue
            after=tuple(c-int(bool(host>>i&1)) for i,c in enumerate(remaining))
            if search(u-cost,after,need-gain,j):
                return True
        return False

    return search(unmarked,caps,target,0)


def copy_pack(left,caps,unmarked,target):
    right=tuple(sum(1<<i for i,mask in enumerate(left) if mask>>j&1) for j in range(7))
    adjacency=tuple(mask<<7 for mask in left)+right
    complement=tuple((127<<7)^mask for mask in adjacency[:7])+tuple(
        127^mask for mask in adjacency[7:])
    remaining_edges=30-unmarked-sum(mask.bit_count() for mask in left)
    rows=[]
    full=16383
    needed=[0]*(full+1)
    for marks in range(1,full+1):
        low=marks&-marks
        needed[marks]=needed[marks^low] | complement[low.bit_length()-1]
        min_host=marks | needed[marks]
        count=marks.bit_count()
        cost=(min_host^marks).bit_count()
        if not 1<=cost<=unmarked or count+cost>9:
            continue
        gain=min(9-cost,count+min(2,count))
        if gain+8*(unmarked-cost)<target:
            continue
        absent=[i for i in range(14) if not min_host>>i&1]
        marked=[i for i in range(14) if marks>>i&1]
        for added in range(min(len(absent),unmarked-cost,9-count-cost)+1):
            u=cost+added
            if min(9-u,count+min(2,count))+8*(unmarked-u)<target:
                continue
            for subset in combinations(absent,added):
                host=min_host | sum(1<<i for i in subset)
                for extra in range(min(2,count,9-u-count)+1):
                    value=count+extra
                    if value+8*(unmarked-u)<target:
                        continue
                    for repeated in combinations(marked,extra):
                        common=tuple((host&adjacency[i]).bit_count() for i in repeated)
                        if any(extra+1+c>3 for c in common):
                            continue
                        copies=sum(1<<i for i in repeated)
                        rows.append((u,marks,host,copies,value,9-u-value))
    rows.sort(key=lambda row:(row[0],-row[4],row[1],row[2],row[3]))
    if not rows:
        return False
    conflicts=[set() for _ in rows]
    for i,j in combinations(range(len(rows)),2):
        _,marks_i,hi,*_=rows[i]
        _,marks_j,hj,*_=rows[j]
        a,b=marks_i&~hj,marks_j&~hi
        if not a or not b:
            continue
        force=False
        missing_edges=0
        for k in range(14):
            if a>>k&1:
                if b&complement[k]:
                    force=True
                    break
                missing_edges+=(b & (127 if k<7 else (127<<7))).bit_count()
        if force or missing_edges>remaining_edges:
            conflicts[i].add(j)
            conflicts[j].add(i)

    bare=[0]*(unmarked+1)
    for u in range(1,unmarked+1):
        bare[u]=max((gain+bare[u-cost] for cost,_,_,_,gain,_ in rows if cost<=u),default=0)

    def visit(u,available,need,prior,extra_cap,blocked,first):
        if need<=0:
            return True
        if bare[u]<need:
            return False
        zero=sum(1<<i for i,c in enumerate(available) if not c)
        too_small=sum(1<<i for i,c in enumerate(available) if c<2)
        no_copies=sum(1<<i for i,c in enumerate(extra_cap) if not c)
        for i in range(first,len(rows)):
            cost,marks,host,copies,value,room=rows[i]
            if (cost>u or bare[u-cost]<need-value or host&zero or copies&too_small
                    or copies&(no_copies|blocked)):
                continue
            if copies.bit_count()==2 and any(c<2 and copies>>j&1 for j,c in enumerate(extra_cap)):
                continue
            forced=[j for j,(old,_) in enumerate(prior) if old in conflicts[i]]
            if len(forced)>room or any(prior[j][1]>=rows[prior[j][0]][5] for j in forced):
                continue
            after=tuple(w-(host>>j&1)-(copies>>j&1) for j,w in enumerate(available))
            next_cap=tuple(c-(copies>>j&1) for j,c in enumerate(extra_cap))
            next_prior=tuple((old,count+(j in forced)) for j,(old,count) in enumerate(prior))
            next_prior+=((i,len(forced)),)
            new_block=blocked | (copies if copies.bit_count()==2 else 0)
            if visit(u-cost,after,need-value,next_prior,next_cap,new_block,i):
                return True
        return False

    return visit(unmarked,caps,target,(),(2,)*14,0,0)


if __name__=="__main__":
    counts=[0,0,0,0,0]
    unresolved=[]
    for unmarked in range(1,31):
        cases={graph for first in first_rows(unmarked) for graph in graphs(*first)}
        for left in sorted(cases):
            checked=verify_one(left,unmarked)
            if checked is None:
                unresolved.append((unmarked,left))
            else:
                counts[checked]+=1
        if cases:
            print(unmarked,len(cases),len(unresolved),flush=True)
    print("Excluded by zero, one, two, or all column capacities:",counts)
    print("First unresolved:",unresolved[:10])
    if counts!=[2,64,11,0,25] or unresolved:
        raise ValueError((counts,unresolved))
