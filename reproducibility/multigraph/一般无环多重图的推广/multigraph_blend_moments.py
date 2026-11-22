"""Finite degree-mixed constraints for the maximum-degree forest flag model."""

from fractions import Fraction as Q

from multigraph_lift_probe import decode, edge_pairs
from multigraph_weighted_ore_model import permutation_slots


def degree_moment_rows(data, mass_low, mass_high):
    """Return exact inequality expressions and flattened Gram coefficient columns."""
    import numpy as np
    from scipy.sparse import csc_matrix, csr_matrix

    orders = data["order"]
    tags = np.asarray([int(mask).bit_count() for mask in data["mask"]])
    order_two = orders == 2
    e = csr_matrix(np.where(order_two & (tags == 1), 2, 0))
    normalizer = csr_matrix(data["normalizer"].astype(np.int64))
    m = csr_matrix(data["twice_obj"].astype(np.int64))
    o0, o1, o2 = [csr_matrix((tags == k)*data["twice_obj"].astype(np.int64)) for k in range(3)]
    geometry = {}
    for n in (3, 4):
        pairs = {edge: i for i, edge in enumerate(edge_pairs(n))}
        choices = []
        perm = np.asarray(permutation_slots(n), dtype=np.int64)
        for row in np.flatnonzero(orders == n):
            colors = np.asarray(decode(n, int(data["code"][row])))
            mask = int(data["mask"][row])
            tag_slots = (1 << perm) & mask
            choices.append((row, colors[perm], tag_slots != 0))
        geometry[n] = pairs, choices

    def moment(n, specification):
        results = np.zeros(len(orders), dtype=np.int64)
        pairs, choices = geometry[n]
        slots = tuple((pairs[tuple(sorted((u, v)))], label) for u, v, label in specification)
        for row, colors, decorated in choices:
            hit = np.ones(len(colors), dtype=np.bool_)
            if tags[row] != sum(label == "tag" for _, label in slots):
                continue
            for slot, label in slots:
                if label == "tag":
                    hit &= decorated[:, slot]
                elif label == "support":
                    hit &= colors[:, slot] > 0
                else:
                    hit &= colors[:, slot] == label
            results[row] = np.count_nonzero(hit)
        return csr_matrix(results)

    second = moment(3, ((0, 1, "tag"), (0, 2, "tag")))
    third = moment(4, tuple((0, v, "tag") for v in (1, 2, 3)))
    blue_neighbor = moment(4, ((0, 1, "support"), (0, 2, "tag"), (1, 3, 1)))
    grams = []
    for c in (1, 2):
        entries = []
        for i in range(4):
            for j in range(4):
                first = (i//2, 2, "tag" if i % 2 else 2)
                second_edge = (j//2, 3, "tag" if j % 2 else 2)
                entries.append(moment(4, ((0, 1, c), first, second_edge)))
        grams.append(entries)
    bridge = sum((g[7] for g in grams), start=csr_matrix(second.shape, dtype=np.int64))
    mixed = sum((g[6] for g in grams), start=csr_matrix(second.shape, dtype=np.int64))
    expressions = [
        ((Q(1, 2), o2), (-2, bridge)),
        ((Q(1, 4), o1), (-2, mixed)),
        ((1, bridge), (1, third), (-1, second)),
        ((2, second), (2, blue_neighbor), (Q(1, 2), o2), (Q(1, 4), o1), (-2, e)),
    ]
    for t in sorted({mass_low, (mass_low+mass_high)/2, mass_high}):
        expressions.append(((t/2, m), (-t*t/2, normalizer), (Q(-1, 2), o0), (Q(-1, 4), o1)))
    grams.append([e, second, second, third])
    from scipy.sparse import hstack
    return expressions, [(hstack([a.T for a in g], format="csc").astype(np.int64), int(len(g)**0.5))
                         for g in grams]
