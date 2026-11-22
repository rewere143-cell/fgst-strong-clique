"""Exact root-spoke relaxation for degree six and a repeated marked pair."""

from functools import lru_cache
from itertools import combinations, combinations_with_replacement, permutations, product
from pathlib import Path
import argparse
import json

SIDE = (0, 0, 0, 0, 1, 1, 1, 1)
PAIRS = tuple(combinations(range(8), 2))
PAIR_INDEX = {pair: i for i, pair in enumerate(PAIRS)}
VERTICES = set(range(8))
PERMS = tuple(permutations(range(4)))
PAIR_TYPES = tuple((i, j, marked) for i, j in PAIRS for marked in (0, 1))
TARGET = 46


def subgroup(unmarked):
    for swap, left, right in product((False, True), PERMS, PERMS):
        perm = tuple(i + 4 * swap for i in left) + tuple(i + 4 * (not swap) for i in right)
        if {perm[v] for v in unmarked} == unmarked:
            yield tuple(
                2 * PAIR_INDEX[tuple(sorted((perm[i], perm[j])))] + marked
                for i, j, marked in PAIR_TYPES
            )


def templates():
    for p in range(5):
        for left in range(p // 2 + 1):
            right = p - left
            unmarked = set(range(left)) | set(range(4, 4 + right))
            seen = set()
            action = tuple(subgroup(unmarked))
            for edge_count in range(5 - p):
                for spec in combinations_with_replacement(range(len(PAIR_TYPES)), edge_count):
                    if spec in seen:
                        continue
                    edges = tuple(PAIR_TYPES[e] for e in spec)
                    if sum(2 - marked for _, _, marked in edges) > 4 - p:
                        continue
                    if any(spec.count(e) > 2 or (e % 2 == 0 and spec.count(e) > 1) for e in spec):
                        continue
                    # Complete marking on a bundle rules out a mixed pair.
                    if any(e % 2 == 0 and e + 1 in spec for e in spec):
                        continue
                    seen.update(tuple(sorted(perm[e] for e in spec)) for perm in action)
                    yield unmarked, edges


def possible_profiles(capacity, neighbors, marked_spokes, loss_limit):
    profiles = {}
    vertices = tuple(range(8))
    require = {
        i: {j for j in marked_spokes - neighbors[i] if SIDE[i] != SIDE[j]}
        for i in vertices
    }
    for size in range(1, 7):
        for active in combinations(vertices, size):
            if any(capacity[i] == 0 for i in active):
                continue
            witnessed = set().union(*(require[i] for i in active)) - set(active)
            loss = len(witnessed)
            if size + loss > 6 or loss > loss_limit:
                continue
            if any(capacity[i] == 0 for i in witnessed):
                continue
            doubled = [i for i in active if capacity[i] >= 2]
            for pairs in range(min(len(doubled), 6 - size - loss) + 1):
                for extra in combinations(doubled, pairs):
                    used = tuple(int(i in active or i in witnessed) + int(i in extra) for i in vertices)
                    profiles[used] = min(loss, profiles.get(used, 8))
    return profiles


def evaluate(unmarked, edges):
    cap = [5] * 8
    adj = [set() for _ in cap]
    for i, j, _ in edges:
        cap[i] -= 1
        cap[j] -= 1
        adj[i].add(j)
        adj[j].add(i)
    marked_spokes = VERTICES - unmarked
    fixed = 2 + len(marked_spokes) + sum(marked for _, _, marked in edges)
    budget = fixed + sum(cap) - TARGET
    assert budget >= 0
    profiles = possible_profiles(cap, adj, marked_spokes, budget)
    table = [
        tuple(sorted(
            ((used, loss) for used, loss in profiles.items() if used[i]),
            key=lambda item: (item[1], -sum(item[0])),
        ))
        for i in range(8)
    ]

    @lru_cache(None)
    def search(rem, slack):
        if not any(rem):
            return True
        if sum(rem[i] for i, options in enumerate(table) if not options) > slack:
            return False
        i = min((i for i, c in enumerate(rem) if c), key=lambda i: (len(table[i]), -rem[i]))
        for used, loss in table[i]:
            if loss <= slack and all(x <= c for x, c in zip(used, rem)):
                if search(tuple(c - x for x, c in zip(used, rem)), slack - loss):
                    return True
        if slack:
            rest = list(rem)
            rest[i] -= 1
            if search(tuple(rest), slack - 1):
                return True
        return False

    feasible = search(tuple(cap), budget)
    return feasible, len(profiles), search.cache_info().currsize


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    cases = []
    for spokes, edges in templates():
        feasible, profiles, nodes = evaluate(spokes, edges)
        cases.append({
            'unmarked_spokes': sorted(spokes), 'internal_edges': edges,
            'relaxation_allows_46': feasible, 'profiles': profiles, 'states': nodes,
        })
    report = {
        'template_count': len(cases),
        'still_possible': sum(row['relaxation_allows_46'] for row in cases),
        'states': sum(row['states'] for row in cases),
        'cases': cases,
    }
    args.output.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    print({k: v for k, v in report.items() if k != 'cases'})


if __name__ == '__main__':
    main()

