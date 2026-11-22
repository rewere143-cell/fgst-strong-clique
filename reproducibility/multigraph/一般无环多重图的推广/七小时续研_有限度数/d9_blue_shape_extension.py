"""Exact connected-component generation for at most eight blue edges."""

from collections import defaultdict
from functools import cache
from itertools import combinations
from itertools import islice

from d9_blue_ferrers_sat import blue_types as small_blue_types
from d9_blue_ferrers_sat import connected_types as brute_connected


def neighbor_masks(n,edges):
    mask=[0]*n
    for u,v in edges:
        mask[u]|=1<<v
        mask[v]|=1<<u
    return tuple(mask)


def refined(mask,cells):
    while True:
        bits=[sum(1<<x for x in part) for part in cells]
        newer=[]
        for part in cells:
            signatures=defaultdict(list)
            for x in part:
                signatures[tuple((mask[x]&b).bit_count() for b in bits)].append(x)
            for key in sorted(signatures,reverse=True):
                newer.append(tuple(signatures[key]))
        result=tuple(newer)
        if len(result)==len(cells):
            return result
        cells=result


def initial_partition(mask):
    parts=defaultdict(list)
    for x,m in enumerate(mask):
        parts[m.bit_count()].append(x)
    return tuple(tuple(parts[d]) for d in sorted(parts,reverse=True))


def twins(mask,x,y):
    return (mask[x]^mask[y])&~((1<<x)|(1<<y))==0


@cache
def canonical(n,edges):
    mask=neighbor_masks(n,edges)
    def search(cells):
        cells=refined(mask,cells)
        if len(cells)==n:
            ordering=[part[0] for part in cells]
            return tuple((u,v) for u,v in combinations(range(n),2)
                         if mask[ordering[u]]&(1<<ordering[v]))
        j=next(k for k,part in enumerate(cells) if len(part)>1)
        part=cells[j]
        choices=[]
        for x in part:
            if any(twins(mask,x,y) for y in choices):
                continue
            choices.append(x)
        return min(search(cells[:j]+((x,),tuple(v for v in part if v!=x))+cells[j+1:])
                   for x in choices)
    return search(initial_partition(mask))


@cache
def inductive_connected(m):
    if m==1:
        return ((2,((0,1),)),)
    found=set()
    for n,edges in inductive_connected(m-1):
        for u in range(n):
            e=tuple(sorted(edges+((u,n),)))
            found.add((n+1,canonical(n+1,e)))
        absent=[e for e in combinations(range(n),2) if e not in edges]
        for e in absent:
            e=tuple(sorted(edges+(e,)))
            found.add((n,canonical(n,e)))
    return tuple(sorted(found))


@cache
def blue_types(m):
    if m<=5:
        return small_blue_types(m)
    catalogue=tuple((j,n,g) for j in range(1,m+1)
                    for n,g in (brute_connected(j) if j<=5 else inductive_connected(j)))
    found=[]
    def combine(start,remaining,items):
        if remaining==0:
            shift=0
            edges=[]
            components=[]
            for n,g in items:
                edges.extend((u+shift,v+shift) for u,v in g)
                components.append((shift,n,g))
                shift+=n
            found.append((shift,tuple(edges),tuple(components)))
            return
        for k in range(start,len(catalogue)):
            j,n,g=catalogue[k]
            if j>remaining:
                break
            combine(k,remaining-j,items+((n,g),))
    combine(0,m,())
    return tuple(sorted(found,key=lambda item:(item[0],item[1])))


@cache
def high_endpoint_types(m, allowed_orders):
    """Blue shapes with specified orders and small total degree excess."""
    excesses={2*m-k for k in allowed_orders if 2<=k<=2*m}
    if not excesses:
        return ()
    max_edges=max(excesses)+1
    if max_edges>8:
        raise ValueError("component bound exceeds eight blue edges")
    catalogue=tuple((j,n,g,2*j-n) for j in range(1,min(m,max_edges)+1)
                    for n,g in (brute_connected(j) if j<=5 else inductive_connected(j))
                    if 2*j-n<=max(excesses))
    found=[]
    def combine(start,remaining,extra,items):
        if remaining==0:
            if extra not in excesses:
                return
            shift=0
            edges=[]
            components=[]
            for n,g in items:
                edges.extend((u+shift,v+shift) for u,v in g)
                components.append((shift,n,g))
                shift+=n
            found.append((shift,tuple(edges),tuple(components)))
            return
        for k in range(start,len(catalogue)):
            j,n,g,cost=catalogue[k]
            if j>remaining:
                break
            if extra+cost<=max(excesses):
                combine(k,remaining-j,extra+cost,items+((n,g),))
    combine(0,m,0,())
    return tuple(sorted(found,key=lambda item:(item[0],item[1])))


def small_automorphisms(n,edges):
    mask=neighbor_masks(n,edges)
    cells=refined(mask,initial_partition(mask))
    cls={v:part for part in cells for v in part}
    order=sorted(range(n),key=lambda v:(len(cls[v]),-mask[v].bit_count(),v))
    def label(pos,partial,taken):
        if pos==n:
            if any(x!=y for x,y in partial.items()):
                yield dict(partial)
            return
        v=order[pos]
        for w in cls[v]:
            if w in taken:
                continue
            if all(bool(mask[v]&(1<<x))==bool(mask[w]&(1<<y))
                   for x,y in partial.items()):
                partial[v]=w
                taken.add(w)
                yield from label(pos+1,partial,taken)
                taken.remove(w)
                del partial[v]
    yield from label(0,{},set())


def symmetry_actions(components):
    previous={}
    for shift,n,edges in components:
        mask=neighbor_masks(n,edges)
        for u in range(n):
            earlier=[v for v in range(u) if twins(mask,u,v)]
            if earlier:
                v=earlier[-1]
                yield {shift+u:shift+v,shift+v:shift+u}
        for mapping in islice(small_automorphisms(n,edges),12):
            yield {shift+u:shift+v for u,v in mapping.items() if u!=v}
        key=(n,edges)
        if key in previous:
            other=previous[key]
            yield {**{shift+u:other+u for u in range(n)},**{other+u:shift+u for u in range(n)}}
        previous[key]=shift


def main():
    for m in range(1,9):
        got=inductive_connected(m)
        if m<=5:
            brute={(n,canonical(n,e)) for n,e in brute_connected(m)}
            if set(got)!=brute:
                raise ValueError(f"connected enumeration disagrees at {m} edges")
        totals={}
        for k,*_ in blue_types(m):
            totals[k]=totals.get(k,0)+1
        filtered=tuple(k for k in totals if 2*m-k<=7)
        if high_endpoint_types(m,filtered)!=tuple(row for row in blue_types(m) if row[0] in filtered):
            raise ValueError(f"high-endpoint enumeration disagrees at {m} edges")
        print(m,len(got),sum(totals.values()),totals)


if __name__=="__main__":
    main()
