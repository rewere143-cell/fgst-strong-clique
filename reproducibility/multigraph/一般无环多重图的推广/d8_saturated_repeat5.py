"""Capacity checks for five saturated repeated marked bundles at maximum degree eight."""

from functools import cache
from itertools import combinations, product
import json


def subsets(size):
    return tuple(tuple(i for i in range(size) if mask>>i&1) for mask in range(1<<size))


def internal_options():
    cross = tuple(product(range(2),range(2,4)))
    for indices in subsets(len(cross)):
        yield tuple(cross[i] for i in indices)


def center_caps(a,internal):
    return tuple(8-a[i]-sum(i in e for e in internal) for i in range(4))


def scalar_candidates():
    for a in product(range(1,8),repeat=4):
        if sum(a)>11:
            continue
        for inside in internal_options():
            if any(a[i]+a[j]<5 for i,j in inside):
                continue
            caps = center_caps(a,inside)
            if min(caps)<0 or sum(caps)+len(inside)<21:
                continue
            leaves = []
            for S in subsets(4)[1:]:
                if any(i in S and j in S for i,j in inside):
                    continue
                cost = max(0,5-min(a[i] for i in S))
                first = [a[i] for i in S if i<2]
                second = [a[i] for i in S if i>=2]
                if first and second:
                    cost = max(cost,10-min(first)-min(second))
                if len(S)+cost<=8:
                    leaves.append((S,cost))

            @cache
            def pack(slots,budget):
                best = 0
                for S,cost in leaves:
                    if cost<=budget and all(slots[i] for i in S):
                        next_slots = tuple(d-(i in S) for i,d in enumerate(slots))
                        best = max(best,len(S)+pack(next_slots,budget-cost))
                return best

            for J in range(21,sum(caps)+len(inside)+1):
                if pack(caps,82-2*J-sum(a))+len(inside)>=J:
                    yield a,inside,J


def ferrers(total):
    for degrees in product(range(1,6),repeat=4):
        rows = (5,)+degrees
        if sum(rows)!=total or tuple(sorted(rows,reverse=True))!=rows:
            continue
        if all(h>=5-i for i,h in enumerate(rows)):
            yield tuple((i,5+j) for i,h in enumerate(rows) for j in range(h))


def consume(slots,used):
    return tuple(value-(i in used) for i,value in enumerate(slots))


def vector_candidate(a,inside,J,core):
    capacities = tuple(7-sum(i in e for e in core) for i in range(10))
    core_sets = subsets(10)
    independent = tuple(S for S in core_sets if 0 not in S and 5 not in S and
                        not any(i in S and j in S for i,j in core))

    def cover(S):
        return all(i in S or j in S for i,j in core)

    choices = [
        tuple((u,)+extra for extra in combinations(range(u+1,u+5),count-1))
        for u,count in zip((0,0,5,5),a)
    ]
    need = J-len(inside)
    caps = center_caps(a,inside)
    demands = tuple(row for row in product(*(range(k+1) for k in caps)) if sum(row)==need)
    for neighbors in product(*choices):
        if any(not cover(set(neighbors[i]) | set(neighbors[j])) for i,j in inside):
            continue
        remaining = tuple(c-sum(i in S for S in neighbors) for i,c in enumerate(capacities))
        if min(remaining)<0:
            continue
        leaf_types = []
        center_neighbors = tuple(set(S) for S in neighbors)
        for S in subsets(4)[1:]:
            if any(i in S and j in S for i,j in inside):
                continue
            forbidden = set().union(*(center_neighbors[i] for i in S))
            possible = []
            for F in sorted(independent,key=len):
                Fset = set(F)
                if len(F)+len(S)>8 or Fset & forbidden or any(not remaining[v] for v in F):
                    continue
                if not all(cover(Fset | center_neighbors[i]) for i in S):
                    continue
                if any(old <= Fset for old in possible):
                    continue
                possible.append(Fset)
                leaf_types.append((S,F))
        by_center = tuple(tuple(row for row in leaf_types if i in row[0]) for i in range(4))

        @cache
        def match(residue,available):
            if not any(residue):
                return True
            i = min((j for j,h in enumerate(residue) if h),key=lambda j: len(by_center[j]))
            for S,F in by_center[i]:
                if all(residue[j] for j in S) and all(available[j] for j in F):
                    if match(consume(residue,S),consume(available,F)):
                        return True
            return False

        if any(match(demand,remaining) for demand in demands):
            return neighbors
    return None


def main():
    possibilities = tuple(scalar_candidates())
    survivors = []
    tried = 0
    for a,inside,J in possibilities:
        for core in ferrers(J-6):
            tried += 1
            model = vector_candidate(a,inside,J,core)
            if model:
                survivors.append(dict(degrees=a,inside=inside,outside_marks=J,
                                      core=core,center_neighbors=model))
    print(json.dumps(dict(scalar_candidates=len(possibilities),tried=tried,survivors=survivors),
                     indent=2),flush=True)


if __name__ == "__main__":
    main()
