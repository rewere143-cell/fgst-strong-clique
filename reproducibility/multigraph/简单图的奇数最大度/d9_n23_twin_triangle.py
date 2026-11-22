"""Degree-nine n=23 saturated triangle with its seven singleton twins.

An exact necessary-condition search for the case in which both the unique
double-neighbor vertex and the third singleton group are saturated.
"""
from collections import Counter
from itertools import product
import json


def type_record(left, right):
    neighbors = left | (right << 6)
    needed = sum(((left >> i & 1) ^ (right >> j & 1)) << (6*i+j)
                 for i,j in product(range(6), repeat=2))
    forbidden = sum((not (left >> i & 1 or right >> j & 1)) << (6*i+j)
                    for i,j in product(range(6), repeat=2))
    return neighbors, needed, forbidden


def solve():
    profiles = [
        type_record(left, right)
        for left,right in product(range(64), repeat=2)
        if left.bit_count()+right.bit_count()==7 and 2<=left.bit_count()<=5
    ]
    row_masks = [63 << (6*i) for i in range(6)]
    column_masks = [sum(1 << (6*i+j) for i in range(6)) for j in range(6)]
    stars = row_masks+column_masks
    rows = []
    for first_size in (2,3):
        first = type_record((1<<first_size)-1, (1<<(7-first_size))-1)
        candidates = [profile for profile in profiles
                      if (profile[1]|first[1]).bit_count()<=23]
        counts = Counter()

        def extend(start, remaining, deg, required, forbidden):
            counts["nodes"] += 1
            if not remaining:
                counts["passing_patterns"] += 1
                return
            for j in range(start,len(candidates)):
                neighbors,force,deny = candidates[j]
                new_required = required | force
                new_forbidden = forbidden | deny
                if new_required.bit_count()>23 or (new_required&new_forbidden).bit_count()>5:
                    continue
                trial=[d+(neighbors>>v&1) for v,d in enumerate(deg)]
                if any(d+(new_required&star).bit_count()>8 for d,star in zip(trial,stars)):
                    continue
                extend(j,remaining-1,trial,new_required,new_forbidden)

        start_neighbors,start_force,start_deny = first
        extend(0,6,[start_neighbors>>v&1 for v in range(12)],start_force,start_deny)
        rows.append(dict(first_size=first_size, candidates=len(candidates), **counts))
    return rows


if __name__=="__main__":
    print(json.dumps(solve(),indent=2))

