"""Compare every tagged forest Gram coefficient on finite weighted hosts."""

import argparse
from collections import Counter, defaultdict
from itertools import permutations, product
import json
from pathlib import Path
from sys import path

from multigraph_lift_probe import decode, edge_pairs
from multigraph_tagged_gram import load_blocks


def direct_maps(colors, n):
    output = defaultdict(list)
    pairs = edge_pairs(n)
    powers = [3**i for i in range(len(pairs)-1)]
    for vertex_map in product(range(len(colors)), repeat=n):
        if colors[vertex_map[0]][vertex_map[1]] != 2:
            continue
        code = sum(colors[vertex_map[i]][vertex_map[j]]*power
                   for (i, j), power in zip(pairs[1:], powers))
        output[code].append(vertex_map)
    return output


def count_automorphisms(n, code, tag_mask):
    original = decode(n, code)
    pairs = edge_pairs(n)
    pair_index = {pair: i for i, pair in enumerate(pairs)}
    tagged = [i for i in range(len(pairs)) if tag_mask >> i & 1]
    result = 0
    for perm in permutations(range(n)):
        indexes = [pair_index[tuple(sorted((perm[u], perm[v])))] for u, v in pairs]
        if all(original[i] == original[j] for i, j in enumerate(indexes)):
            if sum(1 << indexes[i] for i in tagged) == tag_mask:
                result += 1
    assert result and 720 % result == 0
    return result


def tag_weight(weights, vertex_map, tag_mask):
    product_value = 1
    for i, (a, b) in enumerate(edge_pairs(len(vertex_map))):
        if tag_mask >> i & 1:
            product_value *= weights[vertex_map[a]][vertex_map[b]]
    return product_value


def audit(colors, weights, deg, gram, data, old_blocks):
    import numpy as np

    extra = sum(map(sum, weights))//2
    assert extra > 0 and deg > 0
    scale = 720*2*extra*deg**4
    maps = {n: direct_maps(colors, n) for n in range(2, 7)}
    num = np.zeros(gram.shape[0], dtype=np.int64)
    for row, (n, code, tag_mask) in enumerate(zip(data["order"], data["support_code"], data["support_tag_mask"])):
        if not tag_mask:
            continue
        these = maps[n].get(code, ())
        if these:
            total = sum(tag_weight(weights, vertex_map, tag_mask) for vertex_map in these)
            aut = count_automorphisms(int(n), int(code), int(tag_mask))
            num[row] = total*deg**(6-int(n))*(720//aut)

    computed = gram.T @ num
    computed[data["roots"]] += scale
    for variant, ((block, k, code, mask), size, offset) in enumerate(
        zip(data["type_tags"], data["sizes"], data["offsets"])
    ):
        flags = old_blocks[block][1]
        type_maps = maps[k].get(code, ())
        sizes = np.asarray([n for n, _ in flags], dtype=np.int64)
        powers = deg**(6-sizes[:, None]-sizes[None, :]+k)
        expected = np.zeros((size, size), dtype=np.int64)
        counters = [Counter(vertex_map[:k] for vertex_map in maps[n].get(c, ())) for n, c in flags]
        for type_map in type_maps:
            weight = tag_weight(weights, type_map, mask)
            values = np.asarray([counter[type_map] for counter in counters], dtype=np.int64)
            expected += weight*np.outer(values, values)*powers*720
        assert np.array_equal(expected.ravel(), computed[offset:offset+size*size]), (variant, block, k, code, mask)
    return {"vertices": len(colors), "degree": deg, "extra": extra,
            "nonzero_coordinates": int(np.count_nonzero(num)), "checked_gram_entries": gram.shape[1]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("snapshot", type=Path)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("cache", type=Path)
    parser.add_argument("--vendor", type=Path)
    args = parser.parse_args()
    if args.vendor:
        path.insert(0, str(args.vendor))

    import numpy as np
    from scipy.sparse import load_npz

    gram = load_npz(args.cache.with_suffix(".gram.npz"))
    data = dict(np.load(args.cache.with_suffix(".extra.npz")))
    _, blocks, _, _, _ = load_blocks(args.snapshot / "audit" / "flag_coefficients", args.certificate)
    reports = [
        audit([[0, 2], [2, 0]], [[0, 1], [1, 0]], 2, gram, data, blocks),
        audit([[0, 2, 1, 2], [2, 0, 2, 1], [1, 2, 0, 2], [2, 1, 2, 0]],
              [[0, 1, 0, 2], [1, 0, 2, 0], [0, 2, 0, 1], [2, 0, 1, 0]], 6, gram, data, blocks),
    ]
    print(json.dumps(reports, indent=2))


if __name__ == "__main__":
    main()
