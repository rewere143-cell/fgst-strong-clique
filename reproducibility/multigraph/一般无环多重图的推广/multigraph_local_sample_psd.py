"""Lift local bipartite Ore bounds to small categorical sample Gram blocks."""

import argparse
from array import array
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import sys

from multigraph_lift_probe import decode, edge_pairs
from multigraph_sample_gram import categories, model_hashes, neighbors
from multigraph_weighted_ore_model import permutation_slots


def build(cache, support=False):
    import numpy as np
    from scipy.sparse import coo_matrix, save_npz

    data = np.load(cache.with_suffix(".data.npz"))
    flags = {key: i for i, key in enumerate(neighbors())}
    f = len(flags)
    n = 5
    p = np.asarray(permutation_slots(n), dtype=np.int64)
    at = {e: i for i, e in enumerate(edge_pairs(n))}
    r, q = at[0, 1], at[1, 4]
    coords, cols = array("i"), array("i")
    for row in np.flatnonzero(data["order"] == n):
        colors = np.asarray(decode(n, int(data["code"][row])))[p]
        dec = (int(data["mask"][row]) >> p)&1
        attach = (colors[:, q] > 0) if support else (colors[:, q] == 2)
        valid = np.flatnonzero((colors[:, r] == 2)&attach)
        for k in valid:
            c, t = colors[k], dec[k]
            tags = int(t[r])
            choice = []
            for i in (2, 3):
                x, y = at[0, i], at[1, i]
                if not (c[x] or c[y]) or t[x]+t[y] > 1:
                    break
                mode = 0 if t[x] else 1 if t[y] else -1
                choice.append(flags[int(c[x]), int(c[y]), mode])
                tags += int(t[x]+t[y])
            if len(choice) == 2 and tags == int(t.sum()):
                coords.append(row)
                cols.append(int(t[r])*f*f+choice[0]*f+choice[1])
    matrix = coo_matrix((np.ones(len(coords), dtype=np.int64), (coords, cols)),
                        shape=(len(data["order"]), 2*f*f)).tocsr()
    target = ".ore_sample_supportcov.npz" if support else ".ore_sample_qcov.npz"
    save_npz(cache.with_suffix(target), matrix)
    print(json.dumps({"shape": matrix.shape, "nnz": matrix.nnz}))


def hashes(cache):
    return model_hashes(cache) | {
        "qcov": hashlib.sha256(cache.with_suffix(".ore_sample_qcov.npz").read_bytes()).hexdigest(),
    }


def blocks(cache, scale, include):
    from scipy.sparse import csc_matrix, hstack, load_npz

    top, qtop, mass, cross = [load_npz(cache.with_suffix(f".{name}.npz")).tocsc().astype("int64")
                             for name in ("sample_covariance", "ore_sample_qcov",
                                          "sample_categorical", "sample_coupling")]
    f = len(neighbors())
    h = len(categories())
    choices = [categories().index(t) for t in ((0, 1), (0, 2))]
    size = f+len(choices)
    zero = csc_matrix((top.shape[0], 1), dtype="int64")
    for part in sorted(set(include)):
        r, t = divmod(part, 2)
        beta = Q(1, 4) if t else Q(273323, 10**6)
        assert (2*beta*scale).denominator == 1
        contraction = (4*top[:, r*f*f:(r+1)*f*f]-3*qtop[:, r*f*f:(r+1)*f*f])*int(2*beta*scale)
        cells = {}
        for i in range(f):
            for j in range(f):
                cells[i, j] = contraction[:, i*f+j]
            for j, slot in enumerate(choices, f):
                cells[i, j] = cells[j, i] = cross[:, (part*f+i)*h+slot]*scale
        for j, slot in enumerate(choices, f):
            cells[j, j] = mass[:, part*h+slot]*scale
        yield hstack([cells.get((i, j), zero) for i in range(size) for j in range(size)],
                     format="csc"), size


def degree_blocks(cache, scale, include):
    from scipy.sparse import load_npz

    covariance, environment = [load_npz(cache.with_suffix(f".{name}.npz")).tocsc().astype("int64")
                               for name in ("sample_covariance", "ore_sample_qcov")]
    f = len(neighbors())
    for part in sorted(set(include)):
        root, complement = divmod(part, 2)
        slots = slice(root*f*f, (root+1)*f*f)
        base = covariance[:, slots]-environment[:, slots] if complement else environment[:, slots]
        yield base*scale, f


def support_hashes(cache):
    return hashes(cache) | {
        "supportcov": hashlib.sha256(cache.with_suffix(".ore_sample_supportcov.npz").read_bytes()).hexdigest(),
    }


def support_blocks(cache, scale, include):
    from scipy.sparse import load_npz

    covariance, red, support = [load_npz(cache.with_suffix(f".{name}.npz")).tocsc().astype("int64")
                                for name in ("sample_covariance", "ore_sample_qcov", "ore_sample_supportcov")]
    f = len(neighbors())
    for part in sorted(set(include)):
        root, complement = divmod(part, 2)
        slots = slice(root*f*f, (root+1)*f*f)
        base = covariance[:, slots]-support[:, slots] if complement else support[:, slots]-red[:, slots]
        yield base*scale, f


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("cache", type=Path)
    p.add_argument("--vendor", type=Path)
    p.add_argument("--support", action="store_true")
    args = p.parse_args()
    if args.vendor:
        sys.path.insert(0, str(args.vendor))
    build(args.cache, args.support)


if __name__ == "__main__":
    main()
