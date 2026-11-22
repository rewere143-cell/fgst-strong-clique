"""Audit the weighted Ore model on finite hosts, using exact integer replay."""

import argparse
from collections import Counter
import json
from pathlib import Path
import sys

from audit_multigraph_type_forest_psd import direct_maps, tag_weight
from multigraph_lift_probe import edge_pairs
from multigraph_tagged_gram import load_blocks


def audit(colors, weights, matrix, gram, data, metadata, bases, sampling=None, mixed=None,
          localizers=None):
    import numpy as np

    spend = [
        sum((color != 0)+b for color, b in zip(row, tags))
        for row, tags in zip(colors, weights)
    ]
    root_pairs = [(u, v) for u in range(len(colors)) for v in range(u) if colors[u][v] == 2]
    s = len(root_pairs)
    repeat = sum(weights[u][v] for u, v in root_pairs)
    m = s + repeat
    degree_case = bool(data.get("max_degree", False))
    if degree_case:
        assert len(set(spend)) == 1
    sigma = spend[0] if degree_case else max(spend[u]+spend[v] for u, v in root_pairs)
    order = int(max(data["order"]))
    scale = 720*2*m*sigma**(order-2)
    maps = {n: direct_maps(colors, n) for n in range(2, order+1)}
    nums = np.zeros(len(data["order"]), dtype=np.int64)
    for row, (n, c, mask, aut) in enumerate(zip(
        data["order"], data["code"], data["mask"], data["aut_count"],
    )):
        assert 720 % aut == 0
        total = sum(tag_weight(weights, vertex_map, mask) for vertex_map in maps[n].get(c, ()))
        nums[row] = total*int(sigma)**(order-int(n))*(720//aut)
    normalized = int(data["normalizer"] @ nums)
    assert normalized == scale
    valid = matrix @ nums
    if degree_case:
        assert not np.any(valid)
    else:
        assert max(valid) <= 0, np.argmax(valid)
    target = int(data["twice_obj"] @ nums)
    assert target*sigma*sigma == 2*m*scale

    for k, part in enumerate((s*s, 2*s*repeat, repeat*repeat)):
        tag_count = np.asarray([int(mask).bit_count() for mask in data["mask"]])
        isolated = int((data["twice_obj"]*(tag_count == k)) @ nums)
        assert isolated*m*sigma*sigma == 2*part*scale

    computed = gram.T @ nums
    offset = 0
    for size, (block_id, mask), keep in zip(metadata["sizes"], metadata["origins"], metadata["flag_indices"]):
        k, basis = bases[block_id]
        type_code = basis[0][1]
        flags = [basis[i] for i in keep]
        orders = np.asarray([n for n, _ in flags], dtype=np.int64)
        powers = sigma**(order-orders[:, None]-orders[None, :]+k)
        expected = np.zeros((size, size), dtype=np.int64)
        extensions = [Counter(vertex_map[:k] for vertex_map in maps[n].get(c, ())) for n, c in flags]
        for kind in maps[k].get(type_code, ()):
            weight = tag_weight(weights, kind, mask)
            values = np.asarray([extension[kind] for extension in extensions], dtype=np.int64)
            expected += weight*np.outer(values, values)*powers*720
        assert np.array_equal(expected.ravel(), computed[offset:offset+size*size]), (block_id, mask)
        offset += size*size
    report = {"vertices": len(colors), "sigma": sigma, "m": m, "repeat": repeat,
              "checked_inequalities": len(valid), "checked_gram_entries": offset}
    if sampling:
        sample, sample_tag, global_gram, parent, flags = sampling
        for contraction, total in ((sample, m), (sample_tag, repeat)):
            lhs = contraction @ nums
            rhs = 2*total*data["aut_count"][parent]*nums[parent]
            assert np.array_equal(lhs*sigma*sigma, rhs)
        raw = list(map(int, data["aut_count"][flags]*nums[flags]))
        for value, (lhs, rhs) in zip(global_gram.T @ nums, ((x, y) for x in raw for y in raw)):
            assert int(value)*scale*sigma*sigma == 2*m*lhs*rhs
        report["checked_edge_samples"] = len(parent)
        report["checked_global_gram_entries"] = len(flags)**2
    if mixed:
        coefficient_matrix, state = mixed
        direct = coefficient_matrix.T @ nums
        start = 0
        for size, (old, root_tag), remains in zip(state["sizes"], state["origins"], state["flags"]):
            k, flags = bases[old]
            type_code = flags[0][1]
            by_flag = []
            flag_orders = []
            for flag_index, add_weight in remains:
                n, f_code = flags[flag_index]
                counted = Counter()
                for vertex_map in maps[n].get(f_code, ()):
                    w = (sum(weights[vertex_map[u]][vertex_map[v]] for u, v in edge_pairs(n) if v >= k)
                         if add_weight else 1)
                    counted[vertex_map[:k]] += w
                by_flag.append(counted)
                flag_orders.append(n)
            flag_orders = np.asarray(flag_orders, dtype=np.int64)
            powers = sigma**(order-flag_orders[:, None]-flag_orders[None, :]+k)
            expected = np.zeros((size, size), dtype=np.int64)
            for kind in maps[k].get(type_code, ()):
                local = np.asarray([x[kind] for x in by_flag], dtype=np.int64)
                expected += tag_weight(weights, kind, root_tag)*np.outer(local, local)*powers*720
            assert np.array_equal(expected.ravel(), direct[start:start+size**2]), (old, root_tag)
            start += size**2
        report["checked_mixed_gram_entries"] = start
    if localizers:
        contractions, parent_rows, choices = localizers
        evaluated = [a @ nums for a in contractions]
        vertices = range(len(colors))
        for row, (parent, (x, y)) in enumerate(zip(parent_rows, choices)):
            n, c, decoration = data["order"][parent], data["code"][parent], data["mask"][parent]
            expected = [0]*4
            for vertex_map in maps[n].get(c, ()):
                first, second = vertex_map[x], vertex_map[y]
                weight = tag_weight(weights, vertex_map, decoration)
                adjacent_count = sum(colors[second][v] == 2 for v in vertices)
                q_scale = 720*weight*sigma**(order-int(n)-1)
                full_scale = 720*weight*sigma**(order-int(n)-2)
                expected[0] += adjacent_count*q_scale
                expected[1] += adjacent_count**2*full_scale
                for u in vertices:
                    if colors[first][u] == 0 or colors[second][u] or u == second:
                        continue
                    for v in vertices:
                        if colors[u][v] == 2 and not colors[first][v] and not colors[second][v]:
                            expected[2] += full_scale
                            expected[3] += weights[u][v]*full_scale
            assert all(a[row] == expected[j] for j, a in enumerate(evaluated)), (parent, x, y)
        report["checked_localized_ore_entries"] = 4*len(parent_rows)
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("snapshot", type=Path)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("cache", type=Path)
    parser.add_argument("--vendor", type=Path)
    args = parser.parse_args()
    if args.vendor:
        sys.path.insert(0, str(args.vendor))

    import numpy as np
    from scipy.sparse import load_npz

    cache = args.cache
    matrix = load_npz(cache.with_suffix(".ore.npz"))
    gram = load_npz(cache.with_suffix(".gram.npz"))
    data = dict(np.load(cache.with_suffix(".data.npz")))
    metadata = json.loads(cache.with_suffix(".blocks.json").read_bytes())
    _, bases, _, _, _ = load_blocks(args.snapshot / "audit" / "flag_coefficients", args.certificate)
    sampling = None
    if cache.with_suffix(".sample_meta.npz").exists():
        sample_meta = dict(np.load(cache.with_suffix(".sample_meta.npz")))
        sampling = (load_npz(cache.with_suffix(".sample.npz")),
                    load_npz(cache.with_suffix(".sample_tagged.npz")),
                    load_npz(cache.with_suffix(".global_gram.npz")),
                    sample_meta["extension_parents"], sample_meta["gram_flags"])
    inputs = [
        ([[0, 2], [2, 0]], [[0, 1], [1, 0]]),
        ([[0, 2, 1, 0], [2, 0, 2, 1], [1, 2, 0, 2], [0, 1, 2, 0]],
         [[0, 1, 0, 0], [1, 0, 0, 0], [0, 0, 0, 2], [0, 0, 2, 0]]),
    ]
    if bool(data.get("max_degree", False)):
        inputs[-1] = (
            [[0, 2, 1, 2], [2, 0, 2, 1], [1, 2, 0, 2], [2, 1, 2, 0]],
            [[0, 1, 0, 2], [1, 0, 2, 0], [0, 2, 0, 1], [2, 0, 1, 0]],
        )
    mixed = None
    if cache.with_suffix(".mixed_blocks.json").exists():
        mixed = (load_npz(cache.with_suffix(".mixed_gram.npz")),
                 json.loads(cache.with_suffix(".mixed_blocks.json").read_bytes()))
    localizers = None
    if cache.with_suffix(".local_ore_meta.npz").exists():
        labels = ("q_first", "q_second", "plain_ext", "parallel_ext")
        meta = dict(np.load(cache.with_suffix(".local_ore_meta.npz")))
        localizers = ([load_npz(cache.with_suffix(f".{x}.npz")) for x in labels],
                      meta["parents"], meta["roots"])
        pentagon = [[2*int((i-j) % 5 in (1, 4)) for j in range(5)] for i in range(5)]
        if not data.get("max_degree", False):
            pentagon[0][4] = pentagon[4][0] = 1
        inputs.append((pentagon, [[int(color == 2) for color in row] for row in pentagon]))
    report = [audit(colors, weights, matrix, gram, data, metadata, bases,
                    sampling, mixed, localizers)
              for colors, weights in inputs]
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
