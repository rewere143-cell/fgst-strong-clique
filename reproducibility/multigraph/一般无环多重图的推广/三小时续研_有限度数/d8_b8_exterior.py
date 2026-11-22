"""Filter eight-bundle exterior hit profiles by exact degree and deletion conditions."""

from functools import cache
from itertools import combinations
from math import comb

from d8_b9_large_exterior import sorted_hits


def possible_mark_degree(hits):
    return [
        (r if r >= 3 else 0) + min(8-r, sum(r+s >= 8 for j,s in enumerate(hits) if i!=j))
        for i,r in enumerate(hits)
    ]


def eligible_full(hits, marks):
    n = len(hits)
    missing = [n-9+r for r in hits]
    eligible = {i for i,q in enumerate(missing) if q >= (1 if marks[i] >= 8 else 2)}
    while True:
        remove = set()
        for i in eligible:
            partners = sum(j != i and marks[i] + marks[j] < 15 for j in range(n))
            caps = sorted((missing[j]-1 for j in eligible-{i}), reverse=True)
            if partners > sum(caps[:missing[i]]):
                remove.add(i)
        if not remove:
            break
        eligible -= remove
    if len(eligible) < 3:
        return ()
    pairs = sum(marks[i]+marks[j] < 15 for i,j in combinations(range(n),2))
    if pairs > sum(comb(missing[i],2) for i in eligible):
        return ()
    if sum(missing[i] for i in eligible) < 2*n-marks.count(8):
        return ()
    return tuple(sorted(eligible))


@cache
def core_types(bundles, slots):
    """Exterior degree-pair histograms of a full repeated matching."""
    types = [(a,s-a) for s in range(14-bundles)
             if s <= 13-bundles for a in range(s//2+1)]
    def generate(start, count, total):
        if not count:
            if total == 0:
                yield ()
            return
        for i in range(start,len(types)):
            a,b = types[i]
            if count*(a+b) > total or total-(a+b) > (count-1)*(13-bundles):
                continue
            for tail in generate(i,count-1,total-a-b):
                yield (types[i],) + tail

    return tuple(generate(0,bundles,slots))


def cut_upper(bundles, slots, hits):
    threshold = bundles - 6
    ext_bounds = tuple(sum(r >= a+threshold for r in hits) if a else 0
                       for a in range(14-bundles))
    for pattern in core_types(bundles, slots):
        pair_caps = tuple(min(
            max(ext_bounds[a],ext_bounds[b]),
            min(a,ext_bounds[a])+min(b,ext_bounds[b]),
        ) for a,b in pattern)
        threshold_upper = min(
            sum(a for pair in pattern for a in pair if a<j)
            + sum(r for r in hits if r>=j+threshold)
            for j in range(1,15-bundles)
        )
        yield min(sum(pair_caps),threshold_upper)


def profiles(n, p):
    slots = 40-2*p
    for hits in sorted_hits(n,slots,1):
        if hits.count(1) > hits.count(7):
            continue
        if hits.count(2) > hits.count(7)-hits.count(1)+2*hits.count(6):
            continue
        marks = possible_mark_degree(hits)
        if min(marks) < 1:
            continue
        eligible = eligible_full(hits,marks)
        if not eligible:
            continue
        exterior_mark_upper = sum(
            min(8-r,sum(r+s>=8 for j,s in enumerate(hits) if j!=i))
            for i,r in enumerate(hits)
        )//2
        required = 17+slots//2-exterior_mark_upper
        if required > slots or not any(value >= required for value in cut_upper(8,slots,hits)):
            continue
        yield hits,eligible


if __name__ == "__main__":
    import sys
    for p in map(int,sys.argv[1:]) if sys.argv[1:] else range(11,-1,-1):
        counts = [len(list(profiles(n,p))) for n in range(6,(40-2*p)//3+1)]
        print(p,counts,sum(counts),flush=True)
