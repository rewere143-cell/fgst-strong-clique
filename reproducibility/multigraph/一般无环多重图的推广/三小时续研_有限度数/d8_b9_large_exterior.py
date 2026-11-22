"""Integer restrictions for exterior orders at least seven in the nine-bundle case."""

from itertools import combinations
from math import comb


def sorted_hits(n, total, lo=2):
    if n == 0:
        if total == 0:
            yield ()
        return
    for h in range(max(lo, total - 8 * (n-1)), min(8, total//n) + 1):
        for tail in sorted_hits(n-1, total-h, h):
            yield (h,) + tail


def profiles(n, slots):
    for hits in sorted_hits(n, slots):
        marks = [(r if r >= 4 else 0) + min(8-r, sum(
            r + s >= 9 for j, s in enumerate(hits) if j != i
        )) for i, r in enumerate(hits)]
        if min(marks) < 1:
            continue
        if sum(1 for r in hits if r == 2) > hits.count(7):
            continue
        receivers = hits.count(7) - hits.count(2) + 2*hits.count(6)
        if hits.count(3) > receivers:
            continue
        missing = [n - 9 + r for r in hits]
        eligible = {i for i, z in enumerate(missing) if z >= (1 if marks[i] >= 7 else 2)}
        while True:
            remove = set()
            for i in eligible:
                partners = sum(j != i and marks[i] + marks[j] < 14 for j in range(n))
                contributions = sorted((missing[j]-1 for j in eligible - {i}), reverse=True)
                if partners > sum(contributions[:missing[i]]):
                    remove.add(i)
            if not remove:
                break
            eligible -= remove
        if len(eligible) < 3:
            continue
        pairs = sum(marks[i]+marks[j] < 14 for i,j in combinations(range(n),2))
        if pairs > sum(comb(missing[i],2) for i in eligible):
            continue
        yield tuple(hits), tuple(sorted(eligible)), tuple(marks)


if __name__ == "__main__":
    for p in range(4, -1, -1):
        slots = 36 - 2*p
        for n in range(7, slots//4 + 1):
            rows = list(profiles(n, slots))
            print(f"p={p} n={n}: {len(rows)} exterior hit profiles")
            for row in rows:
                print("   ", row)
