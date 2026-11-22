"""Exact relaxation for a hypothetical degree-five strong clique with a parallel marked pair.

The exterior profiles enforce strong adjacency to marked root spokes.
They omit further strong-clique constraints, so the computed optimum is
an upper bound. An attainable profile optimum is not a graph witness.
"""
from functools import lru_cache
from itertools import combinations, combinations_with_replacement, permutations, product
import json

SIDE = (0, 0, 0, 1, 1, 1)
PAIRS = tuple(combinations(range(6), 2))
PERMS = tuple(
    tuple(y + (1 - swap) * 3 for y in p)
    + tuple(y + swap * 3 for y in q)
    for swap in (0, 1)
    for p in permutations(range(3))
    for q in permutations(range(3))
)


def canonical(spokes, edges):
    return min(
        (
            tuple(sorted(perm[v] for v in spokes)),
            tuple(sorted((*sorted((perm[i], perm[j])), marked) for i, j, marked in edges)),
        )
        for perm in PERMS
    )


def partial_templates():
    """Root has two marked parallel edges and six distinct neighbors."""
    seen = set()
    internal_types = tuple((i, j, marked) for i, j in PAIRS for marked in (0, 1))
    for count in range(3):
        for edges in combinations_with_replacement(internal_types, count):
            defect = sum(2 - marked for _, _, marked in edges)
            if defect > 2:
                continue
            for unmarked_count in range(3 - defect):
                for unmarked in combinations(range(6), unmarked_count):
                    key = canonical(unmarked, edges)
                    if key not in seen:
                        seen.add(key)
                        yield key


def exterior_bound(unmarked_spokes, edges):
    cap = [4] * 6
    adjacency = [set() for _ in cap]
    for i, j, _ in edges:
        cap[i] -= 1
        cap[j] -= 1
        adjacency[i].add(j)
        adjacency[j].add(i)
    marked_spokes = set(range(6)) - set(unmarked_spokes)
    profiles = {}
    for marks in product(*(range(c + 1) for c in cap)):
        reward = sum(marks)
        if reward == 0 or reward > 5:
            continue
        required = set()
        for i, marked_count in enumerate(marks):
            if marked_count:
                required.update(
                    j
                    for j in marked_spokes - adjacency[i]
                    if SIDE[i] != SIDE[j]
                )
        used = tuple(max(m, int(i in required)) for i, m in enumerate(marks))
        if sum(used) <= 5 and all(x <= y for x, y in zip(used, cap)):
            profiles[used] = max(reward, profiles.get(used, 0))

    @lru_cache(None)
    def best(remaining):
        result = 0
        for used, reward in profiles.items():
            if all(x <= y for x, y in zip(used, remaining)):
                result = max(
                    result,
                    reward + best(tuple(y - x for x, y in zip(used, remaining))),
                )
        return result

    return 2 + len(marked_spokes) + sum(e[2] for e in edges) + best(tuple(cap))


def main():
    rows = []
    for spokes, edges in partial_templates():
        rows.append(
            {
                "unmarked_spokes": spokes,
                "internal_edges": edges,
                "upper_bound": exterior_bound(spokes, edges),
            }
        )
    report = {
        "template_count": len(rows),
        "maximum_upper_bound": max(row["upper_bound"] for row in rows),
        "templates_allowing_30": [row for row in rows if row["upper_bound"] >= 30],
        "all_templates": rows,
    }
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
