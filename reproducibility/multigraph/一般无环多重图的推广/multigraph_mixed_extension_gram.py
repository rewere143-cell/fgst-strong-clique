"""Couple ordinary and extra-weighted extensions in shared Gram blocks."""

import argparse
from array import array
from collections import defaultdict
import json
from pathlib import Path
import sys
from time import monotonic

from multigraph_lift_probe import decode, edge_pairs
from multigraph_tagged_gram import TaggedGram, load_blocks
from multigraph_weighted_ore_model import bipartite, permutation_slots


def mixed_blocks(source_blocks, order, type_orders, max_degree):
    import numpy as np

    old_count = len(source_blocks)
    largest = max(len(flags) for _, flags in source_blocks)
    base_index = np.full((old_count, largest), -1, dtype=np.int32)
    tag_index = np.full_like(base_index, -1)
    origins, flags_out, sizes = [], [], []
    offsets = np.full((2, old_count), -1, dtype=np.intp)
    n_columns = 0
    size_by_old = np.zeros(old_count, dtype=np.intp)
    for block, (k, flags) in enumerate(source_blocks):
        if k not in type_orders:
            continue
        state = []
        for i, (n, code) in enumerate(flags):
            if 2*n-k > order:
                continue
            color = decode(n, code)
            if not max_degree and not bipartite(n, color):
                continue
            base_index[block, i] = len(state)
            state.append((i, False))
            if any(c == 2 and v >= k for (_, v), c in zip(edge_pairs(n), color)):
                tag_index[block, i] = len(state)
                state.append((i, True))
        if len(state) <= 1:
            continue
        size_by_old[block] = len(state)
        for root_tag in (0, 1):
            offsets[root_tag, block] = n_columns
            n_columns += len(state)**2
            sizes.append(len(state))
            origins.append((block, root_tag))
            flags_out.append(state)
    return base_index, tag_index, offsets, size_by_old, sizes, origins, flags_out, n_columns


def map_for(cache, snapshot, certificate, type_orders):
    import numpy as np
    from scipy.sparse import coo_matrix, save_npz

    started = monotonic()
    data = dict(np.load(cache.with_suffix(".data.npz")))
    arc = snapshot / "audit" / "flag_coefficients"
    gram = TaggedGram(arc, certificate)
    _, source_blocks, _, _, _ = load_blocks(arc, certificate)
    limit = int(max(data["order"]))
    base, tag, offsets, size_by_old, sizes, origins, flag_indices, count = mixed_blocks(
        source_blocks, limit, type_orders, bool(data.get("max_degree", False)),
    )
    groups = defaultdict(list)
    for row, (n, c, mask) in enumerate(zip(data["order"], data["code"], data["mask"])):
        groups[int(n), int(c)].append((int(mask), row))
    perms = {n: np.asarray(permutation_slots(n), dtype=np.intp) for n in range(2, limit+1)}
    rows, columns = array("i"), array("i")

    def append(keys, row_nums, masks, cols):
        if not len(cols):
            return
        guess = np.minimum(np.searchsorted(keys, masks), len(keys)-1)
        correct = keys[guess] == masks
        rows.extend(row_nums[guess[correct]])
        columns.extend(cols[correct])

    for j, ((n, code), by_mask) in enumerate(groups.items()):
        keys, row_nums = np.asarray(sorted(by_mask), dtype=np.int32).T
        raw_perm = perms[n]
        colors = np.asarray(decode(n, code), dtype=np.intp)[raw_perm]
        valid = colors[:, 0] == 2
        perm, colors = raw_perm[valid], colors[valid]
        for k, layout in zip(gram.layout_type_orders[n], gram.layouts[n]):
            if k not in type_orders:
                continue
            left, right, left_slots, right_slots, left_pow, right_pow, left_new, right_new = layout
            l_code = colors[:, left_slots] @ left_pow
            r_code = colors[:, right_slots] @ right_pow
            b_id = left[0][l_code]
            ok = (b_id >= 0) & (b_id == right[0][r_code])
            if not ok.any():
                continue
            block = b_id[ok].astype(np.intp, copy=False)
            p_l = left[1][l_code[ok]].astype(np.intp, copy=False)
            p_r = right[1][r_code[ok]].astype(np.intp, copy=False)
            simple_l, simple_r = base[block, p_l], base[block, p_r]
            include = (size_by_old[block] > 1) & (simple_l >= 0) & (simple_r >= 0)
            if not include.any():
                continue
            block = block[include]
            p_l, p_r = p_l[include], p_r[include]
            simple_l, simple_r = simple_l[include], simple_r[include]
            extra_l, extra_r = tag[block, p_l], tag[block, p_r]
            order_size = size_by_old[block]
            kept_colors = colors[ok][include]
            kept_perm = perm[ok][include]
            for type_weight in (0, 1):
                start = offsets[type_weight, block]
                first_mask = (1 << kept_perm[:, 0]) if type_weight else np.zeros(len(block), dtype=np.int32)
                append(keys, row_nums, first_mask, start+simple_l*order_size+simple_r)
                for e in left_new:
                    left_present = (extra_l >= 0) & (kept_colors[:, e] == 2)
                    left_mask = first_mask | (1 << kept_perm[:, e])
                    append(keys, row_nums, left_mask[left_present],
                           (start+extra_l*order_size+simple_r)[left_present])
                    for f in right_new:
                        both = left_present & (extra_r >= 0) & (kept_colors[:, f] == 2)
                        full = left_mask | (1 << kept_perm[:, f])
                        append(keys, row_nums, full[both],
                               (start+extra_l*order_size+extra_r)[both])
                for f in right_new:
                    right_present = (extra_r >= 0) & (kept_colors[:, f] == 2)
                    right_mask = first_mask | (1 << kept_perm[:, f])
                    append(keys, row_nums, right_mask[right_present],
                           (start+simple_l*order_size+extra_r)[right_present])
        if j and j % 5000 == 0:
            print(f"Weighted extension Gram: {j}/{len(groups)}, {len(rows)} summands", flush=True)

    matrix = coo_matrix(
        (np.ones(len(rows), dtype=np.int32), (rows, columns)),
        shape=(len(data["order"]), count),
    ).tocsr()
    save_npz(cache.with_suffix(".mixed_gram.npz"), matrix)
    cache.with_suffix(".mixed_blocks.json").write_text(json.dumps({
        "sizes": sizes, "origins": origins, "flags": flag_indices,
    })+"\n", encoding="utf-8")
    print(json.dumps({"shape": matrix.shape, "nnz": matrix.nnz, "blocks": len(sizes),
                      "seconds": monotonic()-started}), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("snapshot", type=Path)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("cache", type=Path)
    parser.add_argument("--vendor", type=Path)
    parser.add_argument("--types", nargs="+", type=int, default=[2, 3, 4])
    args = parser.parse_args()
    if args.vendor:
        sys.path.insert(0, str(args.vendor))
    map_for(args.cache, args.snapshot, args.certificate, set(args.types))


if __name__ == "__main__":
    main()
