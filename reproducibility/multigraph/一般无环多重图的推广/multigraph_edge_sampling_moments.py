"""Exact independent marked-edge extensions and global flag Gram coefficients."""

import argparse
from array import array
from collections import defaultdict
import json
from pathlib import Path
import sys
from time import monotonic

from multigraph_lift_probe import decode, edge_pairs
from multigraph_weighted_ore_model import permutation_slots


def decorated_permutations(n, tag, projection):
    selected = [i for i in range(len(edge_pairs(n))) if tag >> i & 1]
    return sum(1 << projection[i] for i in selected)


def build(cache):
    import numpy as np
    from scipy.sparse import coo_matrix, save_npz

    started = monotonic()
    data = dict(np.load(cache.with_suffix(".data.npz")))
    orders, codes, masks = data["order"], data["code"], data["mask"]
    max_order = int(max(orders))
    groups = defaultdict(dict)
    parent_y = []
    gram_flags = []
    extension_index = defaultdict(list)
    gram_index = defaultdict(list)
    for row, (n, code, tag) in enumerate(zip(map(int, orders), map(int, codes), map(int, masks))):
        groups[n, code][tag] = row
        if n+2 <= max_order and tag.bit_count() <= 2:
            extension_index[n, code].append((tag, len(parent_y)))
            parent_y.append(row)
        if 2*n <= max_order and tag.bit_count() <= 1:
            gram_index[n, code].append((tag, len(gram_flags)))
            gram_flags.append(row)
    gram_size = len(gram_flags)
    ext_rows, ext_columns = array("i"), array("i")
    tagged_rows, tagged_columns = array("i"), array("i")
    gram_rows, gram_columns = array("i"), array("i")
    powers = {n: np.asarray([3**i for i in range(len(edge_pairs(n))-1)], dtype=np.intp)
              for n in range(2, max_order+1)}
    perms = {n: np.asarray(permutation_slots(n), dtype=np.intp) for n in range(4, max_order+1)}
    layouts = defaultdict(list)
    for n in range(4, max_order+1):
        idx = {pair: j for j, pair in enumerate(edge_pairs(n))}
        for l in range(2, n-1):
            r = n-l
            left = [idx[pair] for pair in edge_pairs(l)]
            right = [idx[l+u, l+v] for u, v in edge_pairs(r)]
            if r == 2 or (2*l <= max_order and 2*r <= max_order):
                layouts[n].append((l, r, left, right))

    for position, ((n, code), rows) in enumerate(groups.items()):
        if n < 4:
            continue
        colors = np.asarray(decode(n, code), dtype=np.intp)
        perm = perms[n]
        for l, r, left_slots, right_slots in layouts[n]:
            marked = (colors[perm[:, left_slots[0]]] == 2) & (colors[perm[:, right_slots[0]]] == 2)
            left = perm[marked][:, left_slots]
            right = perm[marked][:, right_slots]
            left_codes = colors[left[:, 1:]] @ powers[l]
            right_codes = colors[right[:, 1:]] @ powers[r]
            for subleft, subright, c_left, c_right in zip(left, right, left_codes, right_codes):
                if r == 2:
                    for tag, i in extension_index.get((l, c_left), ()):
                        union = decorated_permutations(l, tag, subleft)
                        for is_tagged, mask in enumerate((union, union | (1 << subright[0]))):
                            j = rows.get(mask)
                            if j is not None:
                                ext_rows.append(i)
                                ext_columns.append(j)
                                if is_tagged:
                                    tagged_rows.append(i)
                                    tagged_columns.append(j)
                for left_tag, i in gram_index.get((l, c_left), ()):
                    tag1 = decorated_permutations(l, left_tag, subleft)
                    for right_tag, j in gram_index.get((r, c_right), ()):
                        union = tag1 | decorated_permutations(r, right_tag, subright)
                        row = rows.get(union)
                        if row is not None:
                            gram_rows.append(row)
                            gram_columns.append(i*gram_size+j)
        if position and position % 3000 == 0:
            print(f"Edge sampling: support {position}/{len(groups)}, "
                  f"extension {len(ext_rows)}, Gram {len(gram_rows)}", flush=True)

    extensions = coo_matrix(
        (np.ones(len(ext_rows), dtype=np.int32), (ext_rows, ext_columns)),
        shape=(len(parent_y), len(orders)),
    ).tocsr()
    tagged_extensions = coo_matrix(
        (np.ones(len(tagged_rows), dtype=np.int32), (tagged_rows, tagged_columns)),
        shape=extensions.shape,
    ).tocsr()
    gram = coo_matrix(
        (np.ones(len(gram_rows), dtype=np.int32), (gram_rows, gram_columns)),
        shape=(len(orders), gram_size**2),
    ).tocsr()
    save_npz(cache.with_suffix(".sample.npz"), extensions)
    save_npz(cache.with_suffix(".sample_tagged.npz"), tagged_extensions)
    save_npz(cache.with_suffix(".global_gram.npz"), gram)
    np.savez(cache.with_suffix(".sample_meta.npz"), extension_parents=parent_y, gram_flags=gram_flags)
    print(json.dumps({"extensions": extensions.shape, "extension_nnz": extensions.nnz,
                      "global_flags": gram_size, "gram_nnz": gram.nnz,
                      "seconds": monotonic()-started}), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("cache", type=Path)
    parser.add_argument("--vendor", type=Path)
    args = parser.parse_args()
    if args.vendor:
        sys.path.insert(0, str(args.vendor))
    build(args.cache)


if __name__ == "__main__":
    main()
