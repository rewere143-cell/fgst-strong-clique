"""Padded blue-spoke and host union constraints for doubled degree-nine roots."""
from collections import defaultdict

from multigraph_lift_probe import decode, edge_pairs, encode
from multigraph_weighted_ore_model import permutation_slots


def repeated_root_neighborhood_rows(data):
    """Multiply repeat-root bounds by each nonnegative root pattern on 2--4 positions."""
    return root_neighborhood_rows(data, 9, union=(15,16), blue=(1,9), requires_tag=True)


def root_neighborhood_rows(data, degree, union, blue=(None,None), requires_tag=False):
    """Bounds for the complete host union and the blue-spoke sum at a marked pair."""
    import numpy as np
    from scipy.sparse import coo_matrix

    coefficients = defaultdict(lambda: defaultdict(lambda: defaultdict(int)))
    for order in (2, 3, 4, 5):
        pairs = tuple(edge_pairs(order))
        slots = {e: i for i, e in enumerate(pairs)}
        layouts = tuple(permutation_slots(order))
        bits = tuple(tuple(1 << pos for pos in layout) for layout in layouts)
        root = slots[0, 1]
        base_pairs = tuple(edge_pairs(order-1))
        base_size = len(base_pairs)
        extend = None if order == 2 else (slots[0, order-1], slots[1, order-1])
        cache = {}
        for column in np.flatnonzero(data["order"] == order):
            color_code = int(data["code"][column])
            if color_code not in cache:
                colors = decode(order, color_code)
                candidates = []
                for layout, layout_bits in zip(layouts, bits):
                    if colors[layout[root]] != 2:
                        continue
                    relabelled = tuple(colors[i] for i in layout)
                    if order <= 4:
                        candidates.append((order, encode(relabelled), layout_bits[root],
                                           layout_bits, 0, 0))
                    if extend is None:
                        continue
                    spokes = tuple(relabelled[i] for i in extend)
                    if not any(spokes):
                        continue
                    old_colors = tuple(relabelled[slots[p]] for p in base_pairs)
                    reached = {0, 1}
                    for _ in range(order-2):
                        for (a, b), value in zip(base_pairs, old_colors):
                            if value and (a in reached or b in reached):
                                reached.update((a, b))
                    if len(reached) < order-1:
                        continue
                    old_bits = tuple(layout_bits[slots[p]] for p in base_pairs)
                    assert len(old_bits) == base_size
                    candidates.append((order-1, encode(old_colors), layout_bits[root],
                                       old_bits, 1, spokes.count(1)))
                cache[color_code] = candidates
            mask = int(data["mask"][column])
            for parent_size, code, root_bit, positions, extension, blue_spokes in cache[color_code]:
                if (requires_tag and not mask & root_bit) or mask & ~sum(positions):
                    continue
                old_mask = sum(1 << i for i, bit in enumerate(positions) if bit & mask)
                block = coefficients[parent_size, code, old_mask]
                for type_, multiplicity in ((1, extension), (2, blue_spokes)) if extension else ((0, 1),):
                    if multiplicity:
                        block[type_][int(column)] += multiplicity

    rows, cols, values = [], [], []
    count = 0
    weights = []
    if blue[0] is not None:
        weights.append((blue[0], 0, -degree))
    if blue[1] is not None:
        weights.append((-blue[1], 0, degree))
    if union[0] is not None:
        weights.append((union[0], -degree, 0))
    if union[1] is not None:
        weights.append((-union[1], degree, 0))
    for types in coefficients.values():
        if not types[0] or not types[1]:
            continue
        # The complete union in a homomorphism extension includes both root images.
        for weight in weights:
            result = defaultdict(int)
            for type_, factor in enumerate(weight):
                if factor:
                    for column, multiplicity in types[type_].items():
                        result[column] += factor*multiplicity
            for column, coef in result.items():
                if coef:
                    rows.append(count)
                    cols.append(column)
                    values.append(coef)
            count += 1
    return coo_matrix((values, (rows, cols)), shape=(count, len(data["order"])),
                      dtype=np.int64).tocsr()
