"""Order-five positivity from a categorical independent marked-edge sample."""

import argparse
from array import array
from itertools import combinations_with_replacement, product
import hashlib
import json
from pathlib import Path
import sys
from time import monotonic

from multigraph_lift_probe import decode, edge_pairs
from multigraph_weighted_ore_model import permutation_slots


def neighbors():
    basis = []
    for a, b in product(range(3), repeat=2):
        if a or b:
            basis.append((a, b, -1))
        if a == 2:
            basis.append((a, b, 0))
        if b == 2:
            basis.append((a, b, 1))
    return basis


def categories():
    return list(combinations_with_replacement(range(9), 2))[1:]


def raw_slices(cache):
    import numpy as np
    from scipy.sparse import coo_matrix, save_npz

    started = monotonic()
    data = dict(np.load(cache.with_suffix(".data.npz")))
    f_index = {x: i for i, x in enumerate(neighbors())}
    h_index = {x: i for i, x in enumerate(categories())}
    f, h = len(f_index), len(h_index)
    lengths = (2*f*f, 4*h, 4*f*h)
    rows = [array("i") for _ in lengths]
    columns = [array("i") for _ in lengths]
    for n in (4, 5):
        ix = {e: i for i, e in enumerate(edge_pairs(n))}
        p = np.asarray(permutation_slots(n), dtype=np.int64)
        for row in np.flatnonzero(data["order"] == n):
            colors = np.asarray(decode(n, int(data["code"][row])))[p]
            decoration = (int(data["mask"][row]) >> p)&1
            tags = decoration.sum(axis=1)
            possible = np.flatnonzero(colors[:, 0] == 2)
            for k in possible:
                c, t = colors[k], decoration[k]
                root_tag = int(t[0])

                def feature(w):
                    e, e2 = ix[0, w], ix[1, w]
                    tagged = int(t[e]+t[e2])
                    if tagged > 1 or not (c[e] or c[e2]):
                        return None, tagged
                    mode = 0 if t[e] else 1 if t[e2] else -1
                    return f_index[int(c[e]), int(c[e2]), mode], tagged

                if n == 4:
                    i, z1 = feature(2)
                    j, z2 = feature(3)
                    if i is not None and j is not None and tags[k] == root_tag+z1+z2:
                        rows[0].append(row)
                        columns[0].append(root_tag*f*f+i*f+j)
                tt = ix[2, 3]
                if c[tt] != 2:
                    continue
                edge_tag = int(t[tt])
                part = root_tag*2+edge_tag
                cross = sorted(int(c[ix[0, z]]+3*c[ix[1, z]]) for z in (2, 3))
                bin_index = h_index.get(tuple(cross))
                if bin_index is None:
                    continue
                if n == 4 and tags[k] == root_tag+edge_tag:
                    rows[1].append(row)
                    columns[1].append(part*h+bin_index)
                if n == 5:
                    f_idx, z3 = feature(4)
                    if f_idx is not None and tags[k] == root_tag+edge_tag+z3:
                        rows[2].append(row)
                        columns[2].append(part*f*h+f_idx*h+bin_index)
    for name, a, b, n_cols in zip(("covariance", "categorical", "coupling"), rows, columns, lengths):
        matrix = coo_matrix((np.ones(len(a), dtype=np.int64), (a, b)),
                            shape=(len(data["order"]), n_cols)).tocsr()
        save_npz(cache.with_suffix(f".sample_{name}.npz"), matrix)
    print(json.dumps({"flags": f, "categories": h, "entries": lengths,
                      "seconds": monotonic()-started}))


def model_hashes(cache):
    return {name: hashlib.sha256(cache.with_suffix(f".sample_{name}.npz").read_bytes()).hexdigest()
            for name in ("covariance", "categorical", "coupling")}


def model_blocks(cache, bounds, scale, active=()):
    import numpy as np
    from scipy.sparse import csr_matrix, hstack, load_npz

    top, mass, cross = [load_npz(cache.with_suffix(f".sample_{name}.npz")).tocsc().astype(np.int64)
                        for name in ("covariance", "categorical", "coupling")]
    f, h = len(neighbors()), len(categories())
    size = f+h+1
    zero = csr_matrix((top.shape[0], 1), dtype=np.int64)
    active = set(active) if active else set(range(4))
    blocks = []
    for part in range(4):
        if part not in active:
            continue
        r, t = divmod(part, 2)
        bound = 2*bounds[t]
        assert (bound*scale).denominator == 1
        lookup = {}
        for i in range(f):
            ci = cross[:, part*f*h+i*h:part*f*h+(i+1)*h]
            cum = csr_matrix(ci.sum(axis=1))*scale
            lookup[i+1, 0] = lookup[0, i+1] = cum
            for j in range(f):
                lookup[i+1, j+1] = top[:, r*f*f+i*f+j]*int(scale*bound)
            for j in range(h):
                v = ci[:, j]*scale
                lookup[i+1, f+1+j] = lookup[f+1+j, i+1] = v
        diag = mass[:, part*h:(part+1)*h]
        lookup[0, 0] = csr_matrix(diag.sum(axis=1))*scale
        for j in range(h):
            v = diag[:, j]*scale
            idx = f+1+j
            lookup[idx, idx] = lookup[0, idx] = lookup[idx, 0] = v
        blocks.append((hstack([lookup.get((i, j), zero) for i in range(size) for j in range(size)],
                              format="csc"), size))
    return blocks


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("cache", type=Path)
    parser.add_argument("--vendor", type=Path)
    args = parser.parse_args()
    if args.vendor:
        sys.path.insert(0, str(args.vendor))
    raw_slices(args.cache)


if __name__ == "__main__":
    main()
