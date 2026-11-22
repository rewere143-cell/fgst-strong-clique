"""Integer triangle-neighborhood profiles for individual degree values."""
from functools import cache
from itertools import combinations
from math import gcd

from multigraph_lift_probe import decode, edge_pairs, encode


def ceil_div(n, d):
    return -(-n//d)


def triangle_profiles(d):
    """A relaxation of (anchor loss, multi-signature vertices, triple-signature vertices)."""
    mass = d*d+(d//2)**2+1
    min_order = ceil_div(2*mass, d)
    maximum_bundle = (2*d*d-mass)//(2*d-1)
    repeat_degree = 2*d-3-ceil_div(mass-2*d+2, d-1)
    exterior = mass-3*d+3
    deficit = 3*d*(d-1)-2*mass
    demand = ceil_div(exterior,d-2)-(d-2)
    kept = set()
    for e in range(deficit//d+1):
        for t in range(3*(d-2)//2+1):
            for q in range(t+1):
                if d*e+2*t+(d+1)*q > deficit:
                    continue
                one = 3*(d-2)-e-2*t-q
                if one < 0:
                    continue
                cap_one = min(((d-1)*one)//2, maximum_bundle*(one*one//3))
                if (d-2)*t-q+cap_one < exterior:
                    continue
                nonzero_support = 3*(d-1)-e-t-q
                if min_order <= nonzero_support:
                    kept.add((e,t,q))
                    continue
                for r in range(1,d-1):
                    if (not t) or (nonzero_support+t*r < min_order):
                        continue
                    room = t*r+deficit-d*(e+t+q)
                    need = max(ceil_div(r,maximum_bundle),r-repeat_degree) * (r+demand-t)
                    if room >= max(0,need):
                        kept.add((e,t,q))
                        break
    # The first coordinate can decrease on padding active-support degrees.
    return sorted({(i,t,q) for e,t,q in kept for i in range(e+1)})


def facets(points):
    """All supporting planes through three affinely independent integer profiles."""
    faces = set()

    def cross(u, v):
        return tuple(u[i]*v[j]-u[j]*v[i] for i,j in ((1,2),(2,0),(0,1)))

    def dot(u, v):
        return sum(a*b for a,b in zip(u,v))

    for a,b,c in combinations(points,3):
        normal = cross(tuple(y-x for x,y in zip(a,b)), tuple(y-x for x,y in zip(a,c)))
        divisor = gcd(*normal)
        if not divisor:
            continue
        normal = tuple(x//divisor for x in normal)
        value = dot(normal,a)
        signs = {int(dot(normal,x) > value)-int(dot(normal,x) < value) for x in points}
        if signs <= {0,-1}:
            faces.add((*normal,value))
        elif signs <= {0,1}:
            faces.add(tuple(-x for x in (*normal,value)))
    return sorted(faces)


@cache
def flag_information(n, code):
    colors = decode(n,code)
    adjacency = [[0]*n for _ in range(n)]
    for (a,b),color in zip(edge_pairs(n),colors):
        adjacency[a][b] = adjacency[b][a] = color
    rows = tuple(tuple(row) for row in adjacency)
    anchors = []
    for a,b,c in combinations(range(n),3):
        if adjacency[a][b] == adjacency[a][c] == adjacency[b][c] == 2:
            anchor = (a,b,c)
            seen_twice = set()
            seen_thrice = set()
            internal_flags = {}
            repeat_spokes = 0
            n_to_anchor = 0
            for x in range(n):
                if x in anchor:
                    continue
                signature = tuple(adjacency[x][i] for i in anchor)
                n_to_anchor = sum(v > 0 for v in signature)
                if n_to_anchor == 3:
                    seen_thrice.add(rows[x])
                elif n_to_anchor == 2 and (1 in signature or rows[x] != rows[anchor[signature.index(0)]]):
                    seen_twice.add(rows[x])
            for i,(u,v) in enumerate(edge_pairs(n)):
                cost = int(u in anchor)+int(v in anchor)
                if cost:
                    internal_flags[i] = (tuple(sorted((rows[u],rows[v]))),cost)
                    if cost == 1:
                        repeat_spokes |= 1 << i
            anchors.append((len(seen_twice),len(seen_thrice),internal_flags,
                            repeat_spokes,n_to_anchor))
    return tuple(anchors)


def finite_triangle_rows(data, degree, scale):
    """Return exact projected hull inequalities and impossible coordinate keys."""
    import numpy as np
    from scipy.sparse import csr_matrix, vstack

    points = triangle_profiles(degree)
    hull = facets(points)
    assert hull
    capacity = {}
    n = len(data["order"])
    vectors = np.zeros((4,n),dtype=np.int64)
    impossible = set()
    for i in np.flatnonzero(data["order"] >= 3):
        order, code, mask = (int(data[key][i]) for key in ("order","code","mask"))
        if order == 3 and code == encode((2,2,2)) and not mask:
            vectors[0,i] = 6
        for lower_two,lower_three,flags,spokes,sig in flag_information(order,code):
            if order == 4:
                if not mask:
                    if sig >= 2:
                        vectors[2,i] += 6
                    if sig == 3:
                        vectors[3,i] += 6
                elif mask.bit_count() == 1 and mask & spokes:
                    vectors[1,i] += 6
            key = lower_two,lower_three
            if key not in capacity:
                capacity[key] = max((e for e,t,q in points if q >= lower_three and t-q >= lower_two),
                                    default=-1)
            contribution = {}
            for pos,(edge,cost) in flags.items():
                if mask & (1 << pos):
                    contribution[edge] = max(cost,contribution.get(edge,0))
            if sum(contribution.values()) > capacity[key]:
                impossible.add((order,code,mask))
    assert np.count_nonzero(vectors[0]) == 1
    rows = []
    for e,t,q,upper in hull:
        # The unlabeled extension includes the three anchored images of signature size two.
        combination = degree*(e*vectors[1]+t*vectors[2]+q*vectors[3])-(upper+3*t)*vectors[0]
        peak = int(np.max(np.abs(combination)))
        if peak:
            rows.append(csr_matrix(combination)*max(1,scale//peak))
    return vstack(rows,format="csr"), impossible
