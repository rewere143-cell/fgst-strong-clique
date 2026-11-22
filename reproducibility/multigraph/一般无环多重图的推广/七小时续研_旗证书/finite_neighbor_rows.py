"""Conditional weighted Mantel constraints on red neighborhoods."""
from collections import defaultdict

from multigraph_lift_probe import decode, edge_pairs, encode
from multigraph_weighted_ore_model import permutation_slots


def weighted_mantel_rows(data):
    """Use red K4-freeness and count ordered pairs with replacement."""
    import numpy as np
    from scipy.sparse import coo_matrix

    terms = defaultdict(lambda: defaultdict(lambda: defaultdict(int)))
    for order in (3, 4, 5):
        base = order-2
        pairs = tuple(edge_pairs(order))
        slots = {edge: i for i, edge in enumerate(pairs)}
        base_slots = tuple(slots[pair] for pair in edge_pairs(base))
        new_slots = slots[0, base], slots[0, base+1]
        between = slots[base, base+1]
        descriptors = []
        for labelling in permutation_slots(order):
            inside = tuple(labelling[j] for j in base_slots)
            leaves = tuple(labelling[j] for j in new_slots)
            inside_bits = tuple(1 << j for j in inside)
            leaf_bits = sum(1 << j for j in leaves)
            allowed = sum(inside_bits) | leaf_bits
            descriptors.append((inside, leaves, labelling[between], inside_bits, leaf_bits, allowed))
        cache = {}
        for row in np.flatnonzero(data["order"] == order):
            code = int(data["code"][row])
            if code not in cache:
                colors = decode(order, code)
                matches = []
                for inside, leaves, link, inside_bits, leaf_bits, allowed in descriptors:
                    if not all(colors[j] == 2 for j in leaves):
                        continue
                    base_colors = tuple(colors[j] for j in inside)
                    if base == 2 and not base_colors[0]:
                        continue
                    if base == 3 and sum(c > 0 for c in base_colors) < 2:
                        continue
                    matches.append((encode(base_colors) if base_colors else 0, inside_bits,
                                    leaf_bits, allowed, 2*int(colors[link] == 2)-1))
                cache[code] = matches
            mask = int(data["mask"][row])
            for base_code, inside_bits, leaf_bits, allowed, value in cache[code]:
                if mask & ~allowed:
                    continue
                base_mask = sum(1 << i for i, bit in enumerate(inside_bits) if mask & bit)
                depth = (leaf_bits & mask).bit_count()
                terms[base, base_code, base_mask][depth][int(row)] += value

    indices, columns, values = [], [], []
    row_number = 0
    for key, monomials in sorted(terms.items()):
        # w=1 always; w=1+b and w=b when both new labels fit the forest budget.
        variants = [(1, 0, 0)]
        if key[-1].bit_count() <= 1:
            variants.extend(((1, 1, 1), (0, 0, 1)))
        for variant in variants:
            counts = defaultdict(int)
            for depth, coefficient in enumerate(variant):
                if coefficient:
                    for column, count in monomials[depth].items():
                        counts[column] += coefficient*count
            terms_row = [(column, count) for column, count in counts.items() if count]
            if not terms_row:
                continue
            for column, count in terms_row:
                indices.append(row_number)
                columns.append(column)
                values.append(count)
            row_number += 1
    return coo_matrix((values, (indices, columns)), shape=(row_number, len(data["order"])),
                      dtype=np.int64).tocsr()
