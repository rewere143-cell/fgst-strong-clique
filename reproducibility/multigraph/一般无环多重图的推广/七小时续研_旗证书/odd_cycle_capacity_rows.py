"""The ordered five-cycle opposite-edge neighborhood bounds."""
from collections import defaultdict
from fractions import Fraction as F

from multigraph_lift_probe import decode, edge_pairs


def cycle_orders(n, code):
    """Every ordering of an induced fully marked C5, with its remaining position."""
    colors = decode(n, code)
    slots = {edge: i for i, edge in enumerate(edge_pairs(n))}

    def slot(a, b):
        return slots[min(a,b), max(a,b)]

    answers = []
    for extra in (range(n) if n == 6 else (None,)):
        cycle = tuple(v for v in range(n) if v != extra)
        neighbors = {v: [w for w in cycle if w != v and colors[slot(v,w)]] for v in cycle}
        if any(len(ns) != 2 for ns in neighbors.values()):
            continue
        if any(colors[slot(v,w)] != 2 for v, ns in neighbors.items() for w in ns):
            continue
        for first in cycle:
            for second in neighbors[first]:
                order = [first, second]
                while len(order) < 5:
                    order.append(next(v for v in neighbors[order[-1]] if v != order[-2]))
                assert len(set(order)) == 5
                edges = tuple(1 << slot(order[i], order[(i+1) % 5]) for i in range(5))
                piece = -1
                neighborhood = False
                if extra is not None:
                    colors_to_root = tuple(colors[slot(extra,i)] for i in order)
                    positive = tuple(i for i,c in enumerate(colors_to_root) if c)
                    if len(positive) == 2 and all(colors_to_root[i] == 2 for i in positive):
                        piece = next((i for i in range(5)
                                      if set(positive) == {(i-1) % 5, (i+1) % 5}), -1)
                    neighborhood = piece == -1 and (colors_to_root[3] or colors_to_root[4])
                answers.append((edges, piece, bool(neighborhood)))
    return answers


def opposite_neighborhood_rows(data, depth, degree_high, delta):
    """Keep asymmetric ordered opposite sides through two in-cycle tags."""
    import numpy as np
    from scipy.sparse import csr_matrix

    parents = defaultdict(lambda: np.zeros(len(data["order"]), dtype=np.int64))
    groups = defaultdict(lambda: np.zeros((6, len(data["order"])), dtype=np.int64))
    for n in (5, 6):
        cache = {}
        for column in np.flatnonzero(data["order"] == n):
            code = int(data["code"][column])
            if n == 5 and code != 6012:
                continue
            mask = int(data["mask"][column])
            if mask.bit_count() > depth:
                continue
            if code not in cache:
                cache[code] = cycle_orders(n, code)
            for edges, piece, neighborhood in cache[code]:
                if mask & ~sum(edges):
                    continue
                anchor_mask = sum(1 << i for i, bit in enumerate(edges) if mask & bit)
                if n == 5:
                    parents[anchor_mask][column] += 1
                    continue
                if piece != -1:
                    groups[anchor_mask][piece, column] += 1
                if neighborhood:
                    groups[anchor_mask][5, column] += 1
    rows = []
    # Round the finite coefficient down, independently of the arithmetic scale.
    extra = F(10000//degree_high, 10000)
    slope = F(1,4)+extra/2
    for mask, parent in sorted(parents.items()):
        a = [csr_matrix(v) for v in groups[mask]]
        p = csr_matrix(parent)
        xi = a[5]
        s1 = p-a[0]-a[2]
        s3 = p-a[2]-a[4]
        s4 = p-a[3]-a[0]
        rows.append(((extra,p), (-F(1),xi)))
        base = ((slope,s1), (-F(1),xi), (-delta,p))
        rows.append(base)
        if mask & ((1 << 2) | (1 << 3)):
            rows.append(base+((extra,s4),))
        if mask & ((1 << 3) | (1 << 4)):
            rows.append(base+((extra,s3),))
    return rows
