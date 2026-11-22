"""Finite degree-nine consequences of a marked triangle."""
from itertools import combinations

from multigraph_lift_probe import decode, edge_pairs, encode


def triangle_profile(n, code, mask):
    """Count the specified anchored extensions, or return None for an impossible flag."""
    colors = decode(n, code)
    adj = [[0]*n for _ in range(n)]
    tagged = set()
    for i, (u, v) in enumerate(edge_pairs(n)):
        adj[u][v] = adj[v][u] = colors[i]
        if mask & (1 << i):
            tagged.update((u, v))
    n_two = n_red_two = n_blue = n_spokes = n_zero_marks = n_pair_marks = n_exclusive_red = 0
    vertices = set(range(n))
    for a, b, c in combinations(range(n), 3):
        if adj[a][b] != 2 or adj[a][c] != 2 or adj[b][c] != 2:
            continue
        anchor = (a, b, c)
        if tagged.intersection(anchor):
            return None
        outer = sorted(vertices.difference(anchor))
        contains_any = []
        signatures = []
        second = None
        for x in outer:
            signature = tuple(adj[x][i] for i in anchor)
            signatures.append(signature)
            available = sum(col > 0 for col in signature)
            contains_any.append(bool(available))
            n_spokes += 6*signature.count(1)
            if available == 1 and 2 in signature:
                n_exclusive_red += 6
            if available == 3:
                return None
            if available != 2:
                continue
            if signature.count(2) == 2:
                root = anchor[signature.index(0)]
                # A fully marked two-signature position is a collapsed anchor.
                if adj[x] != adj[root]:
                    return None
                n_red_two += 6
            else:
                if second is not None and adj[x] != adj[second]:
                    return None
                second = x
                n_two += 6
        if n == 5 and all(contains_any) and adj[outer[0]][outer[1]] == 1:
            n_blue += 12
        if n == 5 and adj[outer[0]][outer[1]] == 2:
            signatures = [tuple(i for i,col in enumerate(signature) if col) for signature in signatures]
            sizes = sorted(len(s) for s in signatures)
            if sizes == [0,2]:
                n_zero_marks += 6
            elif sizes == [1,1] and signatures[0] != signatures[1]:
                n_pair_marks += 6
    return n_two, n_red_two, n_blue, n_spokes, n_zero_marks, n_pair_marks, n_exclusive_red


def triangle_structure(data, scale, spokes=False):
    """Cap blue pairs at 10+4t and count the 0--1 outer two-signature vertices."""
    import numpy as np
    from scipy.sparse import csr_matrix, vstack

    size = len(data["order"])
    allow = np.ones(size, dtype=bool)
    parent = np.zeros(size, dtype=np.int64)
    extra = np.zeros(size, dtype=np.int64)
    red_col = np.zeros(size, dtype=np.int64)
    blue = np.zeros(size, dtype=np.int64)
    spoke_count = np.zeros(size, dtype=np.int64)
    zero = np.zeros(size, dtype=np.int64)
    pair = np.zeros(size, dtype=np.int64)
    exclusive_red = np.zeros(size, dtype=np.int64)
    for i in np.flatnonzero(data["order"] >= 3):
        n = int(data["order"][i])
        code = int(data["code"][i])
        mask = int(data["mask"][i])
        profile = triangle_profile(n, code, mask)
        if profile is None:
            allow[i] = False
        elif not mask:
            if n == 3 and code == encode((2, 2, 2)):
                parent[i] = 6
            elif n == 4:
                extra[i], red_col[i] = profile[:2]
                spoke_count[i] = profile[3]
                exclusive_red[i] = profile[6]
            elif n == 5:
                blue[i] = profile[2]
        if profile is not None and n == 5 and mask.bit_count() <= 1:
            # Any allowed tag in an anchored triangle with two extra positions
            # lies on their sole connecting edge.
            zero[i], pair[i] = profile[4:6]
    assert np.count_nonzero(parent) == 1
    e = csr_matrix(9*red_col-3*parent)*scale
    capped = vstack([csr_matrix(9*extra-parent),
                     csr_matrix(81*blue-72*extra-20*parent)], format="csr")*scale
    if spokes:
        added = vstack([
            csr_matrix(2*parent-9*extra-9*spoke_count),
            csr_matrix(9*spoke_count-5*parent-9*extra-81*zero),
            csr_matrix(81*pair+54*exclusive_red-192*parent),
        ], format="csr")
        # Keep expression scales comparable to the other rows.
        for i in range(added.shape[0]):
            start, stop = added.indptr[i:i+2]
            row = added.data[start:stop]
            row *= scale//max(abs(int(row.min())),abs(int(row.max())))
        capped = vstack([capped,added], format="csr")
    return e, capped, allow
