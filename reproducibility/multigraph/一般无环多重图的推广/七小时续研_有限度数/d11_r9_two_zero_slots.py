"""Exact finite arithmetic for D11, R9, two nonconsecutive zero slots."""

from collections import Counter
from itertools import combinations


TYPES = range(1, 8)
SLOT_BITS = (1, 2, 4)
DOUBLE_TYPES = (3, 5)
HIGH_TYPE = 7


def signature_lists(slots, mask=1, prefix=()):
    if mask not in TYPES:
        yield prefix
        return
    limit = 1 if mask == HIGH_TYPE else 9
    for bit, remaining in zip(SLOT_BITS, slots):
        if mask & bit:
            limit = min(limit, remaining)
    for count in range(limit + 1):
        rest = tuple(remaining - count * bool(mask & bit)
                     for bit, remaining in zip(SLOT_BITS, slots))
        yield from signature_lists(rest, mask + 1, prefix + (mask,) * count)


def floor_blue(signature, slots):
    if signature == HIGH_TYPE:
        return 0
    if signature in DOUBLE_TYPES:
        return 1
    if signature == 1:
        return 2 + min(slots)
    return 2


def blue_profiles(signatures, slots, vertex=0):
    if vertex == len(signatures):
        yield (), ()
        return
    signature = signatures[vertex]
    options = [(floor_blue(signature, slots), -1)]
    if signature in DOUBLE_TYPES:
        options = [(2, -1)] + [(1, index) for index, bit in enumerate(SLOT_BITS)
                               if signature & bit]
    for blue_tail, target_tail in blue_profiles(signatures, slots, vertex + 1):
        for blue, target in options:
            yield (blue,) + blue_tail, (target,) + target_tail


def external_graphs(signatures, targets, sizes, center, threshold):
    possible = []
    for first, second in combinations(range(len(signatures)), 2):
        if signatures[first] | signatures[second] != 7:
            continue
        limit = 10 - center - (signatures[first] & signatures[second]).bit_count()
        if targets[first] >= 0 and targets[first] == targets[second]:
            limit -= sizes[targets[first]] - 1
        possible.append((first, second, limit))
    degrees = [0] * len(signatures)
    selected = []

    def extend(index, edge_count):
        if index == len(possible):
            if edge_count >= threshold:
                yield edge_count, tuple(degrees), tuple(selected)
            return
        if edge_count + 4 * (len(possible) - index) < threshold:
            return
        first, second, limit = possible[index]
        yield from extend(index + 1, edge_count)
        for weight in range(1, 5):
            degrees[first] += weight
            degrees[second] += weight
            valid = degrees[first] + degrees[second] <= limit
            if valid and all(degrees[x] + degrees[y] <= cap
                             for x, y, cap, _ in selected):
                selected.append((first, second, limit, weight))
                yield from extend(index + 1, edge_count + weight)
                selected.pop()
            degrees[first] -= weight
            degrees[second] -= weight
            if not valid:
                break

    yield from extend(0, 0)


def support_cover(edges, order, bound):
    support = tuple((1 << x) | (1 << y) for x, y, _, _ in edges)
    for mask in sorted(range(1 << order), key=int.bit_count):
        if mask.bit_count() > bound:
            break
        if all(pair & mask for pair in support):
            return mask.bit_count()
    return bound + 1


def weak_blue_cover(edges, remaining):
    support = {(x, y) for x, y, _, _ in edges}
    witness_options = []
    for (a, b), (c, d) in combinations(sorted(support), 2):
        if len({a, b, c, d}) != 4:
            continue
        candidates = tuple(tuple(sorted(pair))
                           for pair in ((a, c), (a, d), (b, c), (b, d)))
        if all(pair not in support for pair in candidates):
            witness_options.append(candidates)

    def cover(options, budget):
        if not options:
            return True
        if budget == 0:
            return False
        return any(cover([others for others in options if pair not in others], budget - 1)
                   for pair in options[0])

    return cover(witness_options, remaining)


def survivors(slots):
    center, first_leaf, second_leaf = slots
    sizes = (10 - center, 1 + center, 1 + center)
    product = center * (first_leaf + second_leaf)
    for signatures in signature_lists(slots):
        order = len(signatures)
        if 11 * order - 2 * sum(floor_blue(mask, slots) for mask in signatures) < 41:
            continue
        for blue, targets in blue_profiles(signatures, slots):
            forced_blue = sum(blue)
            blue_budget = (11 * order - 2 * forced_blue - 41) // 2
            if blue_budget < 0:
                continue
            demand = Counter()
            for target in targets:
                if target >= 0:
                    demand[target] += sizes[target] - 1
            total = sum(demand.values())
            old_cost = max(max(demand.values(), default=0), (total + 1) // 2)
            threshold = forced_blue + old_cost + 16 - product
            for marks, degrees, edges in external_graphs(signatures, targets, sizes,
                                                        center, threshold):
                tau = support_cover(edges, order, min(slots))
                if tau > min(slots):
                    continue
                tight = [demand[index] for index, slot in enumerate(slots) if slot == tau]
                blue_old = max(max(tight, default=0), (sum(tight) + 1) // 2)
                if blue_old > blue_budget or not weak_blue_cover(edges, blue_budget - blue_old):
                    continue
                yield signatures, blue, targets, marks, degrees, edges, blue_budget


def check_final_profile(slots, row):
    signatures, blue, targets, marks, degrees, edges, blue_budget = row
    assert slots == (3, 3, 3)
    high = signatures.index(HIGH_TYPE)
    doubles = tuple(i for i, mask in enumerate(signatures) if mask in DOUBLE_TYPES)
    singles = tuple(i for i, mask in enumerate(signatures) if mask in (2, 4))
    assert len(doubles) == len(singles) == 2
    assert tuple(blue[i] for i in singles) == (2, 2) and blue[high] == 0
    pairs = {(x, y) for x, y, _, _ in edges}
    if signatures[doubles[0]] == signatures[doubles[1]]:
        assert marks == 8 and blue_budget == 0 and sum(blue) == 7
        assert degrees[high] == 2
        assert all(degrees[i] == 3 for i in doubles) and all(degrees[i] == 4 for i in singles)
        assert sorted(blue[i] for i in doubles) == [1, 2]
        assert all(tuple(sorted((i, j))) in pairs for i in doubles for j in singles)
        assert any(tuple(sorted((i, high))) in pairs for i in singles)
        assert all(targets[i] == (1 if signatures[i] == 3 else 2)
                   for i in doubles if blue[i] == 1)
        return "coincident"
    assert marks in (7, 8) and blue_budget == 1 and sum(blue) == 6
    assert all(blue[i] == 1 for i in doubles)
    assert {targets[i] for i in doubles} == {1, 2}
    return "distinct"


def main():
    counts = Counter()
    for center in range(1, 8):
        for first_leaf in range(1, (9 - center) // 2 + 1):
            slots = (center, first_leaf, 9 - center - first_leaf)
            result = Counter(check_final_profile(slots, row) for row in survivors(slots))
            counts.update(result)
            print(slots, dict(result))
    assert counts == {"coincident": 16, "distinct": 24}
    print("Remaining finite rows covered by the two final counting arguments:", dict(counts))


if __name__ == "__main__":
    main()
