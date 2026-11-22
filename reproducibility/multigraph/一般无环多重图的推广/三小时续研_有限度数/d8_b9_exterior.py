"""Enumerate the exterior of a 9-bundle degree-eight candidate."""

from collections import Counter
from itertools import combinations
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from d8_repeat_core_sat import graph_orbits


def bounded_compositions(total, lower, caps):
    if not caps:
        if total == 0:
            yield ()
        return
    low = max(lower, total - sum(caps[1:]))
    high = min(caps[0], total - lower * (len(caps) - 1))
    for first in range(low, high + 1):
        for rest in bounded_compositions(total - first, lower, caps[1:]):
            yield (first,) + rest


def exterior_shapes(witness_pairs, order):
    slots = 36 - 2 * witness_pairs
    if order < 4 or 4 * order > slots:
        return
    for _, edges, automorphisms in graph_orbits(order):
        adj = [set() for _ in range(order)]
        for u, v in edges:
            adj[u].add(v)
            adj[v].add(u)
        cap = tuple(8 - len(neighbors) for neighbors in adj)
        for r in bounded_compositions(slots, 2, cap):
            if any(tuple(r[i] for i in p) < r for p in automorphisms):
                continue
            full = {i for i in range(order) if r[i] == cap[i]}
            if len(full) < 3:
                continue
            misses = [full - adj[i] - {i} for i in range(order)]
            if not all(misses):
                continue
            red_possible = tuple(
                (u, v) for u, v in edges
                if r[u] + r[v] >= 9
                and r[u] + r[v] + len((adj[u] | adj[v]) - {u, v}) >= 11
            )
            red_degree_bound = [v if v >= 4 else 0 for v in r]
            for u, v in red_possible:
                red_degree_bound[u] += 1
                red_degree_bound[v] += 1
            if any(bound < (7 if len(miss) == 1 else 1)
                   for bound, miss in zip(red_degree_bound, misses)):
                continue
            if any(red_degree_bound[u] + red_degree_bound[v] < 14
                   for u, v in combinations(range(order), 2)
                   if not misses[u] & misses[v]):
                continue
            yield tuple(edges), tuple(r)


if __name__ == "__main__":
    result = Counter()
    for order in range(4, 7):
        for shape in exterior_shapes(6, order):
            result[order] += 1
            print(order, shape)
    print(result)
