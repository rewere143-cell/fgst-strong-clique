"""Count necessary marking capacity for exterior-degree histograms."""

from functools import cache
from itertools import combinations
import sys

from d8_b8_exterior import core_types


@cache
def exterior_mark_cap(bundles, hits):
    """A degree-constrained graph bound using just exterior hit sums."""
    n = len(hits)
    potential = tuple(
        tuple(j for j in range(i+1,n) if hits[i]+hits[j]>=bundles)
        for i in range(n)
    )

    @cache
    def fill(i, caps):
        if i == n:
            return 0
        available = [j for j in potential[i] if caps[j-i]>0]
        best = fill(i+1,caps[1:])
        for k in range(1,min(caps[0],len(available))+1):
            for subset in combinations(available,k):
                tail = list(caps[1:])
                for j in subset:
                    tail[j-i-1] -= 1
                best = max(best,k+fill(i+1,tuple(tail)))
        return best

    return fill(0,tuple(8-r for r in hits))


def capacity_compatible(bundles, hits, pattern, exterior_max):
    cross_threshold = 12-bundles
    cut_threshold = bundles - 6
    count = bundles
    flats = [a for pair in pattern for a in pair]
    slots = sum(hits)
    p = (bundles*(13-bundles)-slots)//2
    eligible = [sum(r>=j+cut_threshold for r in hits) if j else 0
                for j in range(14-bundles)]
    cut = min(
        sum(min(max(eligible[a],eligible[b]), min(a,eligible[a])+min(b,eligible[b]))
            for a,b in pattern),
        min(
            sum(a for a in flats if a<j) + sum(r for r in hits if r>=j+cut_threshold)
            for j in range(1,15-bundles)
        ),
    )
    can_one = can_two = 0
    for (a,b),(c,d) in combinations(pattern,2):
        can_one += a+c<=cross_threshold
        can_two += max(a+d,b+c)<=cross_threshold
    vertex_bound = sum(
        min(6-a,sum(j!=i and c+a<=cross_threshold for j,(c,d) in enumerate(pattern)))
        for i,pair in enumerate(pattern) for a in pair
    )
    cross = min(can_one + min(p,can_two),vertex_bound//2)
    return count + cross + cut + exterior_max >= 81-bundles


def necessary_patterns(bundles,hits):
    outside = exterior_mark_cap(bundles,tuple(hits))
    for pattern in core_types(bundles,sum(hits)):
        if capacity_compatible(bundles,hits,pattern,outside):
            yield pattern


def low_deletion_survives(bundles, hits, eligible):
    """Can a simple eight-degree vertex survive deleting all low-cut vertices?"""
    low = tuple(r for r in hits if r<bundles-5)
    high = tuple(i for i,r in enumerate(hits) if r>=bundles-5)
    if not low:
        return True
    if sum(8-hits[i] for i in high if max(low)+hits[i]>=bundles) >= 23-bundles:
        return True
    for w in eligible:
        if w not in high:
            continue
        candidates = tuple(i for i in high if i!=w and hits[i]<8)
        for neighbors in combinations(candidates,8-hits[w]):
            capacities = {i:8-hits[i]-int(i in neighbors) for i in candidates}
            for r in low:
                possible = [i for i in candidates if capacities[i]>0 and hits[i]+r>=bundles]
                if not possible:
                    break
                capacities[possible[0]] -= 1
            else:
                return True
    return False


if __name__ == "__main__":
    from d8_b9_large_exterior import profiles
    case_list = len(sys.argv)==3 and sys.argv[1]=="--case-list"
    keys = (int(sys.argv[2]),) if case_list else range(3,-1,-1)
    for p in keys:
        for n in range(4,(36-2*p)//4+1):
            rows = list(profiles(n,36-2*p))
            survivors = [len(tuple(necessary_patterns(9,hits))) 
                         if low_deletion_survives(9,hits,eligible) else 0
                         for hits,eligible,_ in rows]
            if case_list:
                for i, valid in enumerate(survivors):
                    if valid:
                        print(f"p{p}_largen{n}_{i:02d}",flush=True)
            else:
                print(p,n,len(rows),sum(s>0 for s in survivors),sum(survivors),
                      max(survivors,default=0),flush=True)
