"""Degree-loss moments in the bipartite residual of a marked root edge."""

from fractions import Fraction as Q

from multigraph_lift_probe import decode, edge_pairs
from multigraph_weighted_ore_model import permutation_slots


LABELS = ("root", "p", "p2", "p3", "mass", "p_mass", "outside", "excess", "outside_excess")


def loss_coefficients(data):
    """Integer coefficient rows: root plain/tag, residual edge plain/tag, moment."""
    import numpy as np
    from scipy.sparse import csr_matrix

    orders = data["order"]
    limit = len(orders)
    patterns = np.zeros((2, 2, len(LABELS), limit), dtype=np.int64)
    for n in range(2, 6):
        slots = {e: i for i, e in enumerate(edge_pairs(n))}
        perm = np.asarray(permutation_slots(n), dtype=np.int64)
        perm_bits = 1 << perm
        for row in np.flatnonzero(orders == n):
            colors = np.asarray(decode(n, int(data["code"][row])))[perm]
            root = colors[:, slots[0, 1]] == 2
            b = perm_bits[:, slots[0, 1]]
            decoration = int(data["mask"][row])
            p = root.copy()
            for z in range(2, n):
                p &= colors[:, slots[1, z]] == 2
            if n >= 4:
                residual = (root & (colors[:, slots[0, 2]] > 0)
                            & (colors[:, slots[1, 2]] == 0)
                            & (colors[:, slots[0, 3]] == 0)
                            & (colors[:, slots[1, 3]] == 0)
                            & (colors[:, slots[2, 3]] == 2))
                edge = perm_bits[:, slots[2, 3]]
            for root_tag in (0, 1):
                root_mask = root_tag*b
                patterns[root_tag, 0, n-2, row] = np.count_nonzero(
                    p & (decoration == root_mask)
                )
                if n < 4:
                    continue
                for edge_tag in (0, 1):
                    start = root_mask | edge_tag*edge
                    same = residual & (decoration == start)
                    if n == 4:
                        patterns[root_tag, edge_tag, 4, row] = np.count_nonzero(same)
                        continue
                    out = colors[:, slots[1, 4]] > 0
                    patterns[root_tag, edge_tag, 5, row] = np.count_nonzero(
                        same & (colors[:, slots[1, 4]] == 2)
                    )
                    for u in (2, 3):
                        uslot = slots[u, 4]
                        tags = residual & (decoration == (start | perm_bits[:, uslot]))
                        patterns[root_tag, edge_tag, 6, row] += np.count_nonzero(
                            same & out & (colors[:, uslot] > 0)
                        )
                        patterns[root_tag, edge_tag, 7, row] += np.count_nonzero(tags)
                        patterns[root_tag, edge_tag, 8, row] += np.count_nonzero(tags & out)
    return [[dict(zip(LABELS, map(csr_matrix, by_channel)))
             for by_channel in by_edge] for by_edge in patterns]


def local_ore_loss_rows(data, beta, coefficients=None):
    """Return rational inequalities for support and scaled marks in the residual."""
    array = coefficients if coefficients is not None else loss_coefficients(data)
    expressions = []
    for plain, repeated in array:
        cube = 8*plain["root"]-12*plain["p"]+6*plain["p2"]-plain["p3"]
        for weight in (Q(0), Q(1, 2), Q(1)):
            mass_bound = Q(273323, 10**6) if weight == 0 else beta
            for cutoff in (Q(0), Q(1, 8), Q(1, 4), Q(3, 8), Q(1, 2), Q(5, 8), Q(3, 4)):
                items = [(-mass_bound*(1-cutoff)**3/3, cube)]
                for factor, moments in ((Q(1), plain), (weight, repeated)):
                    if not factor:
                        continue
                    items.extend((
                        (factor, moments["outside"]),
                        (factor*(cutoff-1), moments["p_mass"]),
                        (factor*(1-weight), moments["excess"]),
                        (factor*weight, moments["outside_excess"]),
                        (-2*factor*cutoff, moments["mass"]),
                    ))
                expressions.append(tuple(items))
    return expressions
