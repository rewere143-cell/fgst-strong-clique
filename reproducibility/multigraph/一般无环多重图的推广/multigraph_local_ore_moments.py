"""Localize the bipartite residual Ore bound at decorated marked flags."""

import argparse
from array import array
from collections import defaultdict
import json
from pathlib import Path
import sys
from time import monotonic

from multigraph_edge_sampling_moments import decorated_permutations
from multigraph_lift_probe import decode, edge_pairs
from multigraph_weighted_ore_model import permutation_slots


def build(cache):
    import numpy as np
    from scipy.sparse import coo_matrix, save_npz

    started = monotonic()
    data = dict(np.load(cache.with_suffix(".data.npz")))
    orders, codes, masks = data["order"], data["code"], data["mask"]
    order = int(max(orders))
    groups = defaultdict(dict)
    parents = defaultdict(list)
    items, roots = [], []
    for row, (n, code, mask) in enumerate(zip(map(int, orders), map(int, codes), map(int, masks))):
        groups[n, code][mask] = row
        if n+2 > order or mask.bit_count() > 2:
            continue
        for color, (x, y) in zip(decode(n, code), edge_pairs(n)):
            if color != 2:
                continue
            for u, v in ((x, y), (y, x)):
                parents[n, code].append((mask, u, v, len(items)))
                items.append(row)
                roots.append((u, v))

    slots = {n: {pair: i for i, pair in enumerate(edge_pairs(n))} for n in range(2, order+1)}
    perms = {n: np.asarray(permutation_slots(n), dtype=np.intp) for n in range(3, order+1)}
    names = ("q_first", "q_second", "plain_ext", "parallel_ext")
    rows = {name: array("i") for name in names}
    columns = {name: array("i") for name in names}

    def add(name, i, row):
        if row is not None:
            rows[name].append(i)
            columns[name].append(row)

    for z, ((n, code), output) in enumerate(groups.items()):
        if n < 3:
            continue
        colors = np.asarray(decode(n, code), dtype=np.intp)
        perm = perms[n][colors[perms[n][:, 0]] == 2]
        # Original parent support is retained, with one or two fresh positions.
        for count in (1, 2):
            k = n-count
            if k < 2 or k+2 > order:
                continue
            prefix = [slots[n][pair] for pair in edge_pairs(k)]
            projected = perm[:, prefix]
            subcode = colors[projected[:, 1:]] @ np.asarray(
                [3**i for i in range(len(prefix)-1)], dtype=np.intp
            )
            for full, old, c_parent in zip(perm, projected, subcode):
                parent_choices = parents.get((k, c_parent))
                if not parent_choices:
                    continue
                colors_to_first = tuple(int(colors[full[slots[n][v, k]]]) for v in range(k))
                if count == 2:
                    colors_to_second = tuple(int(colors[full[slots[n][v, k+1]]]) for v in range(k))
                    edge_slot = int(full[slots[n][k, k+1]])
                    edge_color = int(colors[edge_slot])
                for mask, x, y, i in parent_choices:
                    mapped = decorated_permutations(k, mask, old)
                    previous = output.get(mapped)
                    if count == 1:
                        if colors_to_first[y] == 2:
                            add("q_first", i, previous)
                        continue
                    if colors_to_first[y] == colors_to_second[y] == 2:
                        add("q_second", i, previous)
                    if (edge_color == 2 and colors_to_first[x] > 0 and not colors_to_first[y]
                            and not colors_to_second[x] and not colors_to_second[y]):
                        add("plain_ext", i, previous)
                        add("parallel_ext", i, output.get(mapped | (1 << edge_slot)))
        if z and z % 5000 == 0:
            print(f"Local Ore coefficients: {z}/{len(groups)}", flush=True)

    coords = []
    for name in names:
        matrix = coo_matrix(
            (np.ones(len(rows[name]), dtype=np.int32), (rows[name], columns[name])),
            shape=(len(items), len(orders)),
        ).tocsr()
        save_npz(cache.with_suffix(f".{name}.npz"), matrix)
        coords.append(matrix.nnz)
    np.savez(cache.with_suffix(".local_ore_meta.npz"), parents=items, roots=roots)
    print(json.dumps({"localizers": len(items), "nonzeros": coords,
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
