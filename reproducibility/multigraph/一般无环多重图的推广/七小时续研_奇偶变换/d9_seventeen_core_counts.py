"""Recompute the role-count bounds for seventeen doubled degree-nine pairs."""

from itertools import combinations_with_replacement
import json
from math import comb


def maximum_external_marks(components, paths, single_edges, center_edges):
    total = single_edges + 2*paths
    assert total == 17
    assert components == single_edges + paths
    core_capacity = 19*paths + 14*single_edges
    baseline = 4*comb(paths,2) + 2*paths*single_edges + comb(single_edges,2)
    center_marks = min(center_edges,paths**2//4)
    best = None
    for center_to_outside in range(5*paths-2*center_edges+1):
        center_to_leaves = 5*paths - 2*center_edges - center_to_outside
        cut = core_capacity - 2*(baseline-3*center_edges-center_to_leaves)
        for n in range(1,cut//(components-6)+1):
            for cut_degrees in combinations_with_replacement(range(components-8,10),n):
                if not 9 <= sum(cut_degrees) <= cut or cut_degrees[-1]+n-1 < 9:
                    continue
                exterior_neighbors = [
                    sum(i != j and degree+other >= components
                        for j,other in enumerate(cut_degrees))
                    for i,degree in enumerate(cut_degrees)
                ]
                # Select how many center neighbors each exterior point uses,
                # retaining only the best charge for each total already used.
                scores = {0:0}
                for degree, exterior in zip(cut_degrees,exterior_neighbors):
                    updated = {}
                    for used,score in scores.items():
                        for hit in range(min(degree,center_to_outside-used)+1):
                            value = 0
                            if hit:
                                leaves = degree-hit if degree >= components-6 else 0
                                value += min(9-hit,leaves+exterior)
                                if degree >= components-4:
                                    value += hit
                            count = used+hit
                            updated[count] = max(updated.get(count,0),score+value)
                    scores = updated
                if center_to_outside in scores:
                    bound = center_marks+7*center_to_leaves+scores[center_to_outside]
                    best = bound if best is None else max(best,bound)
    return best


def main():
    if not __debug__:
        raise RuntimeError("Run with assertions enabled")
    excluded = []
    rows = []
    for c,p,a,minimum,maximum in ((10,7,3,11,17),(9,8,1,10,20)):
        for x in range(minimum,maximum+1):
            upper = maximum_external_marks(c,p,a,x)
            rows.append(dict(components=c,paths=p,center_edges=x,upper=upper))
            if upper is None or upper < 64:
                excluded.append((c,x))
    assert excluded == [(10,x) for x in range(14,18)] + [(9,x) for x in range(17,21)]
    print(json.dumps(dict(rows=rows,excluded=excluded),indent=2))


if __name__ == "__main__":
    main()
