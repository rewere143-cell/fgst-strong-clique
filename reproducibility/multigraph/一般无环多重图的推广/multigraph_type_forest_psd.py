"""Generate all shared-type forest Gram constraints through order six."""

import argparse
from array import array
from collections import defaultdict
from itertools import combinations, permutations
import json
from pathlib import Path
import sys
from time import monotonic

from multigraph_affine_lift_search import build, forest
from multigraph_lift_probe import decode, edge_pairs
from multigraph_tagged_gram import TaggedGram


def pair_mask(tag, pairs):
    return sum(1 << pairs.index(edge) for edge in tag)


def type_menu(gram, degree):
    menus = defaultdict(dict)
    sizes, offsets, roots, types = [], [], [], []
    n_coordinates = 0
    n_blocks = len(gram.types)
    for block, (k, code) in enumerate(gram.types):
        pairs = edge_pairs(k)
        red = [i for i, color in enumerate(decode(k, code)) if color == 2]
        assert red[0] == 0
        choices = [
            (0,)+chosen for count in range(min(degree, len(red))) for chosen in combinations(red[1:], count)
        ]
        size = int(gram.sizes[block])
        for chosen in choices:
            mask = sum(1 << i for i in chosen)
            if not forest(pairs, mask, k):
                continue
            if chosen not in menus[k]:
                menus[k][chosen] = [-1]*n_blocks
            menus[k][chosen][block] = n_coordinates
            sizes.append(size)
            offsets.append(n_coordinates)
            types.append((block, k, code, mask))
            if k == 2:
                roots.append(n_coordinates)
            n_coordinates += size**2
    return menus, sizes, offsets, roots, types, n_coordinates


def build_map(snapshot, certificate, out, vary_plain, degree):
    import numpy as np
    from scipy.sparse import coo_matrix, save_npz

    start = monotonic()
    variables = []
    a, b, cost, metadata, orders, faces, tags, rhs_exact, scale, restricted, a_exact, c_exact = build(
        snapshot, certificate, face_only=False, boolean=False, profiles=True, monomials=True,
        multiplier_degree=degree, test_degree=degree+1, vary_plain=vary_plain,
        record_metadata=True, retain_zero_rows=True, variable_metadata=variables,
    )
    assert len(metadata) == a.shape[0] == len(b)
    assert not restricted.any()
    gram = TaggedGram(snapshot / "audit" / "flag_coefficients", certificate)
    menus, sizes, offsets, roots, types, packed = type_menu(gram, degree+1)
    support = defaultdict(list)
    support_codes, support_tags = array("i"), array("i")
    for row, (n, code, tag) in enumerate(metadata):
        mask = pair_mask(tag, edge_pairs(n))
        support_codes.append(code)
        support_tags.append(mask)
        if tag:
            support[n, code].append((mask, row))

    permutations_by_order = {}
    pair_slots_by_order = {}
    for n in range(3, 7):
        pairs = edge_pairs(n)
        slots = {pair: i for i, pair in enumerate(pairs)}
        pair_slots_by_order[n] = slots
        permutations_by_order[n] = np.asarray([
            [slots[tuple(sorted((perm[u], perm[v])))] for u, v in pairs]
            for perm in permutations(range(n))
        ], dtype=np.intp)
    menus_by_order = {}
    for n, slots in pair_slots_by_order.items():
        menus_by_order[n] = {}
        for k in (2, 3, 4):
            if n < k:
                continue
            pairs = edge_pairs(k)
            menus_by_order[n][k] = [
                (np.asarray([slots[pairs[i]] for i in chosen], dtype=np.intp),
                 np.asarray(offset_list, dtype=np.int64))
                for chosen, offset_list in menus[k].items()
            ]

    rows, columns = array("i"), array("i")
    for j, ((n, code), tagged_rows) in enumerate(support.items()):
        keys, row_ids = np.asarray(sorted(tagged_rows), dtype=np.int32).T
        perm = permutations_by_order[n]
        colors = np.asarray(decode(n, code), dtype=np.intp)[perm]
        valid = colors[:, 0] == 2
        colors = colors[valid]
        perm = perm[valid]
        for k, layout in zip(gram.layout_type_orders[n], gram.layouts[n]):
            left, right, left_slots, right_slots, left_pow, right_pow, _, _ = layout
            l_code = colors[:, left_slots] @ left_pow
            r_code = colors[:, right_slots] @ right_pow
            blocks = left[0][l_code]
            keep = (blocks >= 0) & (blocks == right[0][r_code])
            if not keep.any():
                continue
            blocks = blocks[keep].astype(np.intp, copy=False)
            a_i = left[1][l_code[keep]].astype(np.intp, copy=False)
            a_j = right[1][r_code[keep]].astype(np.intp, copy=False)
            local = a_i*gram.sizes[blocks]+a_j
            perm_keep = perm[keep]
            for tag_slots, variant_offsets in menus_by_order[n][k]:
                tag_offset = variant_offsets[blocks]
                allowed = tag_offset >= 0
                if not allowed.any():
                    continue
                masks = np.bitwise_or.reduce(1 << perm_keep[allowed][:, tag_slots], axis=1)
                observed = np.minimum(np.searchsorted(keys, masks), len(keys)-1)
                identified = keys[observed] == masks
                if not identified.any():
                    continue
                rows.extend(row_ids[observed[identified]])
                columns.extend((tag_offset[allowed]+local[allowed])[identified])
        if j % 5000 == 0:
            print(f"Type forest Gram map: {j}/{len(support)}, contributions {len(rows)}", flush=True)

    rc = (np.frombuffer(rows, dtype=np.int32), np.frombuffer(columns, dtype=np.int32))
    gram_map = coo_matrix((np.ones(len(rows), dtype=np.int32), rc),
                          shape=(len(metadata), packed)).tocsr()
    arrays = dict(
        rhs=b, objective=cost, order=orders, face=faces, tag_size=tags, exact_rhs=rhs_exact,
        exact_objective=c_exact, scale=scale, offsets=np.asarray(offsets),
        sizes=np.asarray(sizes), roots=np.asarray(roots), type_tags=np.asarray(types),
        support_code=np.asarray(support_codes), support_tag_mask=np.asarray(support_tags),
        degree_metadata=np.asarray(variables, dtype=np.int32),
    )
    save_npz(out.with_suffix(".npz"), a)
    save_npz(out.with_suffix(".exact.npz"), a_exact)
    save_npz(out.with_suffix(".gram.npz"), gram_map)
    np.savez(out.with_suffix(".extra.npz"), **arrays)
    print(json.dumps({"degree": a.shape, "gram": gram_map.shape, "gram_nonzero": gram_map.nnz,
                      "blocks": len(sizes), "seconds": monotonic()-start}), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("snapshot", type=Path)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("cache", type=Path)
    parser.add_argument("--vendor", type=Path)
    parser.add_argument("--vary-plain", action="store_true")
    parser.add_argument("--degree", type=int, choices=(1, 2), default=2)
    args = parser.parse_args()
    if args.vendor:
        sys.path.insert(0, str(args.vendor))
    build_map(args.snapshot, args.certificate, args.cache, args.vary_plain, args.degree)


if __name__ == "__main__":
    main()
