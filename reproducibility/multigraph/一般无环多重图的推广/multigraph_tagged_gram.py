"""Tagged contractions of existing PSD blocks for multigraph flag experiments.

Numerators have the input certificate's common denominator. For a support
representative F, a table entry is the contribution to the moment with one
tagged edge, multiplied by |Aut(F)|. It counts the original Gram gluing
summands, marking the image of the type's pair 01 in each summand.
"""

from collections import defaultdict
from itertools import combinations, permutations
from pathlib import Path
import argparse
import json
import sys

from multigraph_lift_probe import decode, edge_pairs, read_ints


def load_blocks(data, certificate_path):
    certificate = json.loads(certificate_path.read_text())
    lines = iter((data / "basis.txt").read_text().splitlines())
    num_variables, block_count = map(int, next(lines).split())
    blocks = []
    offsets = []
    weights = []
    for _ in range(block_count):
        k, type_code, size = map(int, next(lines).split())
        flags = [tuple(map(int, next(lines).split())) for _ in range(size)]
        assert flags[0] == (k, type_code)
        blocks.append((k, flags))
        offsets.append(len(weights))
        weights.extend([0] * (size * size))
    for factor in certificate["rank_one_factors"]:
        j = int(factor["block"])
        weight = int(factor["weight_numerator"])
        vector = list(map(int, factor["vector_numerators"]))
        assert weight >= 0 and len(vector) == len(blocks[j][1])
        size = len(vector)
        for i, x in enumerate(vector):
            if x:
                for h, y in enumerate(vector):
                    if y:
                        weights[offsets[j] + i * size + h] += weight * x * y
    return num_variables, blocks, offsets, weights, int(certificate["common_denominator"])


class TaggedGram:
    def __init__(self, data, certificate_path):
        import numpy as np

        self.np = np
        self.num_variables, blocks, offsets, weights, self.scale = load_blocks(
            data, certificate_path
        )
        # The compact certificate is fast in int64. Keep exact Python integers
        # for larger certificates and for sums where int64 would overflow.
        maximum = max(map(abs, weights))
        dtype = np.int64 if 720 * maximum < 2**63 else object
        self.weights = np.asarray(weights, dtype=dtype)
        self.extension_dtype = np.int64 if 18000 * maximum < 2**63 else object
        self.block_count = len(blocks)
        self.types = [(k, flags[0][1]) for k, flags in blocks]
        self.offsets = np.asarray(offsets, dtype=np.intp)
        self.sizes = np.asarray([len(flags) for _, flags in blocks], dtype=np.intp)
        self.order_two_blocks = tuple(j for j, (k, _) in enumerate(blocks) if k == 2)
        self.root = [
            weights[offsets[j]] if k == 2 else 0
            for j, (k, _) in enumerate(blocks)
        ]

        # A type order greater than two determines its block by its exact
        # code. Type order two occurs twice, so use a separate map for each.
        groups = defaultdict(list)
        for j, (k, _) in enumerate(blocks):
            groups[(k, j if k == 2 else -1)].append(j)
        self.layouts = defaultdict(list)
        self.layout_type_orders = defaultdict(list)
        for (k, _), group in groups.items():
            maps = {}
            for j in group:
                for flag_index, (n, code) in enumerate(blocks[j][1]):
                    if n not in maps:
                        length = 3 ** (len(edge_pairs(n)) - 1)
                        maps[n] = (
                            np.full(length, -1, dtype=np.int16),
                            np.full(length, -1, dtype=np.int32),
                        )
                    block_map, flag_map = maps[n]
                    assert block_map[code] < 0
                    block_map[code] = j
                    flag_map[code] = flag_index
            for left, left_maps in maps.items():
                for right, right_maps in maps.items():
                    n = left + right - k
                    pairs = {pair: i for i, pair in enumerate(edge_pairs(n))}
                    left_positions = range(left)
                    right_positions = list(range(k)) + list(range(left, n))
                    left_cols = [pairs[e] for e in combinations(left_positions, 2)][1:]
                    right_cols = [pairs[e] for e in combinations(right_positions, 2)][1:]
                    left_new = [pairs[e] for e in combinations(left_positions, 2) if e[1] >= k]
                    right_new = [pairs[e] for e in combinations(right_positions, 2) if e[1] >= k]
                    self.layouts[n].append((
                        left_maps, right_maps, left_cols, right_cols,
                        np.asarray([3**i for i in range(len(left_cols))], dtype=np.intp),
                        np.asarray([3**i for i in range(len(right_cols))], dtype=np.intp),
                        left_new, right_new,
                    ))
                    self.layout_type_orders[n].append(k)

    def matched_products(self, n, permuted, pair_map):
        np = self.np
        rooted = permuted[:, 0] == 2
        colors = permuted[rooted]
        rooted_pairs = pair_map[rooted]
        for layout in self.layouts[n]:
            left_map, right_map, left_cols, right_cols, left_pow, right_pow, left_new, right_new = layout
            left_codes = colors[:, left_cols] @ left_pow
            right_codes = colors[:, right_cols] @ right_pow
            left_block = left_map[0][left_codes]
            right_block = right_map[0][right_codes]
            keep = (left_block >= 0) & (left_block == right_block)
            if not np.any(keep):
                continue
            block = left_block[keep].astype(np.intp, copy=False)
            i = left_map[1][left_codes[keep]]
            j = right_map[1][right_codes[keep]]
            flat = self.offsets[block] + i * self.sizes[block] + j
            yield block, self.weights[flat], colors[keep], rooted_pairs[keep], left_new, right_new

    def coefficients(self, n, permuted, pair_map):
        """Return exact integer numerators indexed by (edge slot, block)."""
        np = self.np
        output = np.zeros((len(edge_pairs(n)), self.block_count), dtype=self.weights.dtype)
        for block, weight, _, pairs, _, _ in self.matched_products(n, permuted, pair_map):
            np.add.at(output, (pairs[:, 0], block), weight)
        return output

    def extension_coefficients(self, n, permuted, pair_map):
        """Return blockwise corrections L and K for (f+a*g)^T Q (f+a*g).

        Here f is the original flag function and g sums its one-edge tags
        on marked edges incident to extension positions. The correction is
        a*L + a**2*K. Index K by sorted pairs of distinct edge slots.
        """
        np = self.np
        width = len(edge_pairs(n))
        # Summing over all eligible extension edges adds at most 25
        # contributions per permutation. Avoid machine overflow even for
        # the alternative certificates with large denominators.
        linear = np.zeros((width, self.block_count), dtype=self.extension_dtype)
        quadratic = np.zeros((width, width, self.block_count), dtype=self.extension_dtype)
        for block, weight, colors, pairs, left, right in self.matched_products(n, permuted, pair_map):
            for e in left + right:
                keep = colors[:, e] == 2
                np.add.at(linear, (pairs[keep, e], block[keep]), weight[keep])
            for e in left:
                for f in right:
                    keep = (colors[:, e] == 2) & (colors[:, f] == 2)
                    a, b = pairs[keep, e], pairs[keep, f]
                    np.add.at(quadratic, (np.minimum(a, b), np.maximum(a, b), block[keep]), weight[keep])
        return linear, quadratic


def audit(data, certificate, samples, check_extension):
    """Compare the sum over tag positions with the old untagged Gram data."""
    import numpy as np

    gram = TaggedGram(data, certificate)
    reference = {}
    indexes = {}
    for n in range(3, 7):
        path = data / (f"idx{n}.bin" if n < 6 else "order6_orbit_index.bin")
        index = read_ints(path, "i")
        offset = 728 if n == 6 else 0
        representatives = {}
        for code, idx in enumerate(index):
            if idx >= 0:
                representatives.setdefault(idx + offset, code)
        items = sorted(representatives.items())
        if 1 < samples < len(items):
            items = [items[(len(items) - 1) * i // (samples - 1)] for i in range(samples)]
        indexes[n] = items
        reference.update((idx, [0] * gram.block_count) for idx, _ in items)

    from bisect import bisect_right

    for key, value in zip(read_ints(data / "keys.bin", "q"), read_ints(data / "values.bin", "i")):
        row, idx = divmod(key, gram.num_variables)
        if idx in reference:
            j = bisect_right(gram.offsets, row) - 1
            reference[idx][j] += int(gram.weights[row]) * value

    for n, items in indexes.items():
        pairs = edge_pairs(n)
        location = {e: i for i, e in enumerate(pairs)}
        pair_map = np.asarray([
            [location[tuple(sorted((permutation[u], permutation[v])))] for u, v in pairs]
            for permutation in permutations(range(n))
        ])
        for idx, code in items:
            original = np.asarray(decode(n, code))
            permuted = original[pair_map]
            aut = int(np.count_nonzero(np.all(permuted == original, axis=1)))
            tagged = gram.coefficients(n, permuted, pair_map).sum(axis=0)
            assert tagged.tolist() == [aut * value for value in reference[idx]], (n, code, idx)
            if check_extension:
                linear, quadratic = gram.extension_coefficients(n, permuted, pair_map)
                extra = np.arange(len(pairs)) % 3
                products = (extra[:, None] * extra[None, :]).reshape(-1)
                actual = (
                    extra @ linear.astype(object)
                    + products @ quadratic.reshape(-1, gram.block_count).astype(object)
                )
                expected = [0] * gram.block_count
                for blocks, weights, colors, slots, left, right in gram.matched_products(n, permuted, pair_map):
                    for j, weight, pattern, permutation in zip(blocks, weights, colors, slots):
                        left_sum = sum(int(extra[permutation[e]]) for e in left if pattern[e] == 2)
                        right_sum = sum(int(extra[permutation[e]]) for e in right if pattern[e] == 2)
                        expected[j] += int(weight) * ((1 + left_sum) * (1 + right_sum) - 1)
                assert actual.tolist() == expected, (n, code, idx, 'extension corrections')
        print(f"order {n}: {len(items)} blockwise exact Gram identities", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("data", type=Path)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("--vendor", type=Path)
    parser.add_argument("--samples", type=int, default=257)
    parser.add_argument("--check-extension", action='store_true')
    args = parser.parse_args()
    if args.vendor:
        sys.path.insert(0, str(args.vendor))
    audit(args.data, args.certificate, args.samples, args.check_extension)


if __name__ == "__main__":
    main()

