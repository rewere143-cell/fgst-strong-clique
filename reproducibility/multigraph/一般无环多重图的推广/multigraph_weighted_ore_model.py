"""Finite weighted marked-bipartite Ore-degree moment relaxation."""

import argparse
from collections import defaultdict
from fractions import Fraction
from itertools import permutations
import json
from pathlib import Path
import sys
from time import monotonic

from multigraph_lift_probe import decode, edge_pairs
from multigraph_tagged_gram import load_blocks


def bipartite(n, colors):
    neighbors = [[] for _ in range(n)]
    for color, (u, v) in zip(colors, edge_pairs(n)):
        if color == 2:
            neighbors[u].append(v)
            neighbors[v].append(u)
    side = [-1]*n
    for vertex in range(n):
        if side[vertex] >= 0:
            continue
        side[vertex] = 0
        pending = [vertex]
        while pending:
            x = pending.pop()
            for y in neighbors[x]:
                if side[y] == side[x]:
                    return False
                if side[y] < 0:
                    side[y] = 1-side[x]
                    pending.append(y)
    return True


def permutation_slots(n):
    pairs = edge_pairs(n)
    index = {edge: i for i, edge in enumerate(pairs)}
    return [[index[tuple(sorted((p[u], p[v])))] for u, v in pairs]
            for p in permutations(range(n))]


def standard_gram(snapshot, certificate, orders, codes, masks, aut_count):
    import numpy as np
    from scipy.sparse import coo_matrix

    directory = snapshot / "audit" / "flag_coefficients"
    n_variables, blocks, offsets, weights, _ = load_blocks(directory, certificate)
    ids = {n: np.fromfile(directory / f"idx{n}.bin", dtype="<i4") for n in range(3, 6)}
    ids[6] = np.fromfile(snapshot / "flags" / "order6_orbit_index.bin", dtype="<i4") + 728
    gram_keys = np.fromfile(directory / "keys.bin", dtype="<i8")
    gram_values = np.fromfile(directory / "values.bin", dtype="<i4")
    matrix_column, old_index = np.divmod(gram_keys, n_variables)
    convert = np.full(n_variables, -1, dtype=np.int32)
    multipliers = np.zeros(n_variables, dtype=np.int32)
    for y in np.flatnonzero((masks == 0) & (orders > 2)):
        idx = ids[orders[y]][codes[y]]
        convert[idx] = y
        multipliers[idx] = aut_count[y]
    keep = convert[old_index] >= 0
    rows = convert[old_index[keep]]
    columns = matrix_column[keep]
    data = gram_values[keep]*multipliers[old_index[keep]]
    root = int(np.flatnonzero((masks == 0) & (orders == 2))[0])
    root_cols = [offsets[j] for j, (k, _) in enumerate(blocks) if k == 2]
    matrix = coo_matrix(
        (np.r_[data, [2]*len(root_cols)],
         (np.r_[rows, [root]*len(root_cols)], np.r_[columns, root_cols])),
        shape=(len(orders), len(weights)),
    ).tocsc()
    return matrix, blocks, offsets


def reduce_gram(plain, tagged, data, blocks, plain_offsets, order):
    import numpy as np
    from scipy.sparse import hstack

    choices = []
    for j, (k, flags) in enumerate(blocks):
        choices.append((plain, plain_offsets[j], k, flags, (j, 0)))
    for (j, k, _, mask), offset in zip(data["type_tags"], data["offsets"]):
        choices.append((tagged, offset, k, blocks[j][1], (j, mask)))
    reduced, sizes, origins, flag_indices = [], [], [], []
    for matrix, offset, k, flags, origin in choices:
        size = len(flags)
        keep = [
            i for i, (n, _) in enumerate(flags)
            if 2*n-k <= order and matrix.indptr[offset+i*(size+1)+1] > matrix.indptr[offset+i*(size+1)]
        ]
        if not keep:
            continue
        use = np.asarray(keep, dtype=np.intp)
        chosen = offset + size*use[:, None] + use[None, :]
        reduced.append(matrix[:, chosen.ravel()])
        sizes.append(len(keep))
        origins.append(origin)
        flag_indices.append(keep)
    return hstack(reduced, format="csr"), sizes, origins, flag_indices


def assemble(snapshot, certificate, raw, out, order, max_degree):
    import numpy as np
    from scipy.sparse import coo_matrix, csr_matrix, load_npz, save_npz, vstack

    started = monotonic()
    raw_data = dict(np.load(raw.with_suffix(".extra.npz")))
    raw_degree = load_npz(raw.with_suffix(".exact.npz")).tocsr()
    scale = int(raw_data["scale"])
    assert not np.any(raw_degree.data % scale)
    raw_degree.data //= scale
    raw_orders, raw_codes, raw_masks = (
        raw_data["order"], raw_data["support_code"], raw_data["support_tag_mask"],
    )
    plain_root_raw = np.flatnonzero((raw_orders == 2) & (raw_masks == 0))
    assert len(plain_root_raw) == 1
    raw_degree.data[raw_degree.indptr[plain_root_raw[0]]:raw_degree.indptr[plain_root_raw[0]+1]] *= 2
    raw_degree = vstack((raw_degree, csr_matrix(2*raw_data["exact_objective"]//scale)), format="csr")

    # Whole-support bipartiteness is sufficient; the sides need not be
    # retained as labels since every red-edge map respects some bipartition.
    legal = {}
    for n, code in set(zip(map(int, raw_orders), map(int, raw_codes))):
        legal[n, code] = n <= order and (max_degree or bipartite(n, decode(n, code)))
    y_kept = np.asarray([legal[n, c] for n, c in zip(raw_orders, raw_codes)])
    y_kept = np.r_[y_kept, True]
    orders = np.r_[raw_orders, 2][y_kept]
    codes = np.r_[raw_codes, 0][y_kept]
    masks = np.r_[raw_masks, 1][y_kept]
    degree_metadata = list(map(tuple, raw_data["degree_metadata"]))
    eq_keep = np.asarray([k < order and legal[k, c] for k, c, u, tag in degree_metadata])
    eq_index = {key: j for j, key in enumerate(key for key, keep in zip(degree_metadata, eq_keep) if keep)}
    degree = -raw_degree[y_kept][:, eq_keep].T.tocsr()

    row_groups = defaultdict(list)
    for row, key in enumerate(zip(orders, codes)):
        row_groups[key].append(row)
    support_lookup = {key: decode(*key) for key in row_groups}
    if not max_degree:
        ore_first, ore_second, ore_parent, ore_value = [], [], [], []
        for key, first in eq_index.items():
            n, code, u, tag = key
            color = support_lookup[n, code]
            start, end = degree.indptr[first:first+2]
            earlier = [j for j in range(start, end) if orders[degree.indices[j]] == n]
            assert len(earlier) == 1
            parent_col = degree.indices[earlier[0]]
            parent_value = degree.data[earlier[0]]
            assert parent_value < 0
            for (x, y), c in zip(edge_pairs(n), color):
                if x == u and c == 2:
                    ore_first.append(first)
                    ore_second.append(eq_index[n, code, y, tag])
                    ore_parent.append(parent_col)
                    ore_value.append(-parent_value)
        ore_added = coo_matrix(
            (ore_value, (np.arange(len(ore_parent)), ore_parent)),
            shape=(len(ore_parent), degree.shape[1]),
        )
        ore = degree[ore_first] + degree[ore_second] + ore_added
        degree = vstack((degree, ore), format="csr")

    perm = {n: np.asarray(permutation_slots(n), dtype=np.intp) for n in range(2, order+1)}
    aut_count = np.zeros(len(orders), dtype=np.int32)
    twice_obj = np.zeros(len(orders), dtype=np.int32)
    for n, c in support_lookup:
        colors = np.asarray(support_lookup[n, c], dtype=np.intp)
        table = perm[n]
        orbit_rows = row_groups[n, c]
        identity = np.all(colors[table] == colors, axis=1)
        if n == 4:
            target_keep = (colors[table[:, 0]] == 2) & (colors[table[:, -1]] == 2)
            goal_masks = (1 << table[target_keep, 0]) | (1 << table[target_keep, -1])
        for row in orbit_rows:
            tag = masks[row]
            used = [i for i in range(len(colors)) if tag >> i & 1]
            if used:
                images = np.bitwise_or.reduce(1 << table[identity][:, used], axis=1)
                aut_count[row] = np.count_nonzero(images == tag)
            else:
                aut_count[row] = int(np.count_nonzero(identity))
            if n == 4:
                twice_obj[row] = np.count_nonzero((goal_masks & tag) == tag)
    assert np.all(aut_count > 0)
    normalizer = np.where(orders == 2, aut_count, 0)

    # New model contains both root masses, so constant order-two Gram
    # contributions become columns with coefficient |Aut(R_2)|=2.
    tagged = load_npz(raw.with_suffix(".gram.npz"))
    tag_root = coo_matrix(
        ([2]*len(raw_data["roots"]), ([0]*len(raw_data["roots"]), raw_data["roots"])),
        shape=(1, tagged.shape[1]),
    )
    tagged = vstack((tagged, tag_root), format="csr")[y_kept].tocsc()
    plain, blocks, plain_offsets = standard_gram(snapshot, certificate, orders, codes, masks, aut_count)
    gram, sizes, origins, flag_indices = reduce_gram(plain, tagged, raw_data, blocks, plain_offsets, order)
    out.with_suffix(".blocks.json").write_text(json.dumps({
        "sizes": sizes, "origins": [tuple(map(int, origin)) for origin in origins],
        "flag_indices": flag_indices,
    })+"\n", encoding="utf-8")
    save_npz(out.with_suffix(".ore.npz"), degree)
    save_npz(out.with_suffix(".gram.npz"), gram)
    np.savez(out.with_suffix(".data.npz"), normalizer=normalizer, twice_obj=twice_obj,
             order=orders, code=codes, mask=masks, aut_count=aut_count,
             max_degree=np.bool_(max_degree))
    print(json.dumps({
        "order": order, "inequalities": degree.shape[0], "atoms": degree.shape[1],
        "ore_nnz": degree.nnz, "gram_nnz": gram.nnz, "blocks": len(sizes),
        "max_block": max(sizes), "seconds": monotonic()-started,
    }), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("snapshot", type=Path)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("raw", type=Path)
    parser.add_argument("out", type=Path)
    parser.add_argument("--vendor", type=Path)
    parser.add_argument("--order", type=int, choices=(4, 5, 6), default=5)
    parser.add_argument("--max-degree", action="store_true")
    args = parser.parse_args()
    if args.vendor:
        sys.path.insert(0, str(args.vendor))
    assemble(args.snapshot, args.certificate, args.raw, args.out, args.order, args.max_degree)


if __name__ == "__main__":
    main()
