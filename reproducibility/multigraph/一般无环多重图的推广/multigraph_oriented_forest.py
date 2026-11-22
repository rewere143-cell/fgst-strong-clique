"""Degree and independent-edge moments for the oriented extra-support pseudoforest."""

import argparse
from array import array
from itertools import permutations
import json
from pathlib import Path
import sys
from time import monotonic

from multigraph_lift_probe import decode, edge_pairs
from multigraph_weighted_ore_model import permutation_slots


def possible_direction(n, colors, edges, extra, reverse):
    """Check the equalities forced by a positive outdegree-one decoration."""
    ufs = list(range(n))

    def root(v):
        while ufs[v] != v:
            v = ufs[v]
        return v

    directions = [(v, u) if reverse & (1 << e) else (u, v)
                  for e, (u, v) in enumerate(edges) if extra & (1 << e)]
    while True:
        heads = {}
        merged = False
        for u, v in directions:
            x, y = root(u), root(v)
            if x == y:
                return False
            if x in heads and root(heads[x]) != y:
                ufs[y] = root(heads[x])
                merged = True
            else:
                heads[x] = y
        if not merged:
            break
    quotient = {}
    for (u, v), c in zip(edges, colors):
        x, y = sorted((root(u), root(v)))
        if x == y:
            if c:
                return False
            continue
        if (x, y) in quotient and quotient[x, y] != c:
            return False
        quotient[x, y] = c
    return True


def geometry(n):
    import numpy as np

    vertices = np.asarray(list(permutations(range(n))), dtype=np.int64)
    edges = edge_pairs(n)
    u, v = np.asarray(edges).T
    slots = np.asarray(permutation_slots(n), dtype=np.int64)
    flip = (vertices[:, u] > vertices[:, v]).astype(np.int64)
    bits = 1 << np.arange(len(edges), dtype=np.int64)
    return edges, slots, flip, bits


def orientations(colors, mask, n, tables):
    import numpy as np

    edges, slots, flip, bits = tables
    possible = [0]
    for e in range(len(edges)):
        if (mask >> e) & 1:
            possible += [x | (1 << e) for x in possible]
    tag_sets = (mask >> slots) & 1
    aut = (np.all(colors[slots] == colors, axis=1) & ((tag_sets @ bits) == mask))
    tag_aut = tag_sets[aut]
    for reverse in possible:
        maps = ((((reverse >> slots[aut]) & 1) ^ flip[aut]) & tag_aut) @ bits
        if (maps < reverse).any() or not possible_direction(n, colors, edges, mask, reverse):
            continue
        yield reverse, int(np.count_nonzero(maps == reverse))


def matrix(cache, out, max_order=None):
    import numpy as np
    from scipy.sparse import coo_matrix, save_npz

    started = monotonic()
    data = dict(np.load(cache.with_suffix(".data.npz")))
    source_size = len(data["order"])
    limit = min(max_order or 5, max(data["order"]))
    are_orders = data["order"]
    geom = {n: geometry(n) for n in range(2, limit+1)}
    source = {}
    fibers = {}
    owner, reverse, aut, arity = [], [], [], []
    row_diagonal = []
    extension_parents = []
    degree_len = 0
    for i in np.flatnonzero(are_orders <= limit):
        n, c, mask = (int(data[key][i]) for key in ("order", "code", "mask"))
        source[n, c, mask] = i
        colors = np.asarray(decode(n, c))
        refs = {}
        for d, a in orientations(colors, mask, n, geom[n]):
            idx = len(owner)
            refs[d] = idx
            owner.append(i)
            reverse.append(d)
            aut.append(a)
            arity.append(n)
            retain_degree = n < limit and mask.bit_count() <= 2
            row_diagonal.append(degree_len if retain_degree else -1)
            if retain_degree:
                degree_len += n
            if n+2 <= limit:
                extension_parents.append(idx)
        assert refs
        fibers[i] = refs
    print(f"{len(owner)} orientations over {len(source)} undirected atoms, "
          f"{degree_len} degree equations, {len(extension_parents)} sampled parents", flush=True)

    eq_i, eq_j, eq_v = array("i"), array("i"), array("i")
    edge_rows, edge_cols = array("i"), array("i")
    tag_rows, tag_cols = array("i"), array("i")
    sample_index = {i: j for j, i in enumerate(extension_parents)}
    for i, (n, a, row) in enumerate(zip(arity, aut, row_diagonal)):
        if row >= 0:
            for v in range(n):
                eq_i.append(row+v)
                eq_j.append(i)
                eq_v.append(-a)
    for n in range(3, limit+1):
        edges, slots, flip, bits = geom[n]
        slots_by_pair = {e: i for i, e in enumerate(edges)}
        for source_idx in np.flatnonzero(are_orders == n):
            c, mask = (int(data[key][source_idx]) for key in ("code", "mask"))
            orig = np.asarray(decode(n, c))
            raw = slots[orig[slots[:, 0]] == 2]
            trans = flip[orig[slots[:, 0]] == 2]
            colors = orig[raw]
            all_tags = (mask >> raw) & 1
            degree_transitions = []
            sample_transitions = []
            for removed in (1, 2):
                k = n-removed
                if k < 2:
                    continue
                prefix = [slots_by_pair[e] for e in edge_pairs(k)]
                parent_mask = all_tags[:, prefix] @ bits[:len(prefix)]
                parent_code = colors[:, prefix[1:]] @ (3**np.arange(len(prefix)-1, dtype=np.int64))
                missing = all_tags.sum(1)-all_tags[:, prefix].sum(1)
                candidates = missing <= 1
                if removed == 2:
                    pair = slots_by_pair[k, k+1]
                    candidates &= (colors[:, pair] == 2) & (missing == all_tags[:, pair])
                for p in np.flatnonzero(candidates):
                    old = source.get((k, int(parent_code[p]), int(parent_mask[p])))
                    if old is None:
                        continue
                    remap = tuple(int(raw[p, e]) for e in prefix)
                    flipping = sum(int(trans[p, e]) << j for j, e in enumerate(prefix))
                    entry = old, int(parent_mask[p]), remap, flipping
                    if removed == 2:
                        sample_transitions.append((entry, bool(all_tags[p, pair])))
                    else:
                        new_slots = [slots_by_pair[v, k] for v in range(k)]
                        choose = all_tags[p, new_slots] if missing[p] else colors[p, new_slots] > 0
                        if choose.any():
                            degree_transitions.append((entry, tuple(map(int, np.flatnonzero(choose)))))
            for d, child in fibers[source_idx].items():
                def parent_of(entry):
                    old, tags, indices, flipping = entry
                    projected = sum(((d >> j) & 1) << e for e, j in enumerate(indices))
                    return fibers[old].get((projected ^ flipping) & tags)
                for entry, vertices in degree_transitions:
                    parent = parent_of(entry)
                    if parent is not None and row_diagonal[parent] >= 0:
                        row = row_diagonal[parent]
                        for v in vertices:
                            eq_i.append(row+v)
                            eq_j.append(child)
                            eq_v.append(1)
                for entry, tagged in sample_transitions:
                    parent = parent_of(entry)
                    if parent is not None:
                        i = sample_index[parent]
                        edge_rows.append(i)
                        edge_cols.append(child)
                        if tagged:
                            tag_rows.append(i)
                            tag_cols.append(child)
    n_col = len(owner)
    distinct = coo_matrix((np.ones(n_col, dtype=np.int32), (owner, np.arange(n_col))),
                          shape=(source_size, n_col)).tocsr()
    degree = coo_matrix((eq_v, (eq_i, eq_j)), shape=(degree_len, n_col)).tocsr()
    for name, i, j in (("sample", edge_rows, edge_cols), ("sample_tag", tag_rows, tag_cols)):
        grid = coo_matrix((np.ones(len(i), dtype=np.int32), (i, j)),
                          shape=(len(extension_parents), n_col)).tocsr()
        save_npz(out.with_suffix(f".{name}.npz"), grid)
    save_npz(out.with_suffix(".split.npz"), distinct)
    save_npz(out.with_suffix(".degree.npz"), degree)
    np.savez(out.with_suffix(".data.npz"), owner=owner, reverse=reverse, aut=aut, arity=arity,
             sample_parent=extension_parents, row_diagonal=row_diagonal)
    print(json.dumps({"variables": n_col, "projection": distinct.shape,
                      "degree_nnz": degree.nnz, "seconds": monotonic()-started}), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("cache", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--vendor", type=Path)
    parser.add_argument("--order", type=int, choices=(3, 4, 5))
    args = parser.parse_args()
    if args.vendor:
        sys.path.insert(0, str(args.vendor))
    matrix(args.cache, args.output, args.order)


if __name__ == "__main__":
    main()
