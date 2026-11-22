"""Gram matrices conditioned on the orientation of extra parallel support."""

import argparse
from array import array
from fractions import Fraction as Q
from itertools import product
import json
from pathlib import Path
import sys

from multigraph_lift_probe import decode
from multigraph_oriented_forest import geometry


def flags():
    out = [(0, 0, -1, 0)]
    for a, b in product(range(3), repeat=2):
        if not (a or b):
            continue
        out.append((a, b, -1, 0))
        for i, c in enumerate((a, b)):
            if c == 2:
                out.extend((a, b, i, direction) for direction in (0, 1))
    return out


def build(data, oriented):
    import numpy as np
    from scipy.sparse import coo_matrix

    basis = {flag: i for i, flag in enumerate(flags())}
    size = len(basis)
    by_order = {n: geometry(n) for n in range(2, 5)}
    shape = (len(oriented["owner"]), size*size*2)
    row, col = array("i"), array("i")
    for idx, (source, direction, n) in enumerate(zip(
        oriented["owner"], oriented["reverse"], oriented["arity"],
    )):
        n = int(n)
        if n > 4:
            continue
        pairs, perms, flip, _ = by_order[n]
        codes = np.asarray(decode(n, int(data["code"][source])))
        tag = int(data["mask"][source])
        pos = np.flatnonzero(codes[perms[:, 0]] == 2)
        cmap = {e: i for i, e in enumerate(pairs)}
        for p in pos:
            slot = perms[p]
            mask = (tag >> slot) & 1
            rev = ((direction >> slot) & 1)^flip[p]
            if mask[0] and rev[0]:
                continue
            if n == 4 and mask[cmap[2, 3]]:
                continue
            found = []
            for v in range(2, n):
                i, j = cmap[0, v], cmap[1, v]
                a, b = codes[slot[i]], codes[slot[j]]
                if not (a or b) or mask[i]+mask[j] > 1:
                    break
                if mask[i]:
                    found.append(basis[a, b, 0, rev[i]])
                elif mask[j]:
                    found.append(basis[a, b, 1, rev[j]])
                else:
                    found.append(basis[a, b, -1, 0])
            if len(found) != n-2:
                continue
            if n == 2:
                selections = [(0, 0)]
            elif n == 3:
                selections = [(found[0], 0), (0, found[0])]
            else:
                selections = [found]
            for i, j in selections:
                row.append(idx)
                col.append(int(mask[0])*size*size+i*size+j)
    matrix = coo_matrix((np.ones(len(row), dtype=np.int64), (row, col)),
                        shape=shape).tocsr()
    return matrix, size


def direct(colors, extra, direction):
    """Read the Gram matrix as exact per-root weighted rank-one sums."""
    n = len(colors)
    degree = sum(c > 0 for c in colors[0])+sum(extra[0])
    mass = sum((c == 2)+b for row, w in zip(colors, extra) for c, b in zip(row, w))//2
    basis = flags()
    size = len(basis)
    output = [[0]*(size*size) for _ in range(2)]
    for u, v in product(range(n), repeat=2):
        if colors[u][v] != 2:
            continue
        root_weights = (1, extra[u][v] if (u, v) in direction else 0)
        vector = [degree]+[0]*(size-1)
        for k, (a, b, at, reverse) in enumerate(basis[1:], 1):
            for w in range(n):
                if colors[u][w] != a or colors[v][w] != b:
                    continue
                if at < 0:
                    vector[k] += 1
                else:
                    x = (u, v)[at]
                    edge = (w, x) if reverse else (x, w)
                    if edge in direction:
                        vector[k] += extra[x][w]
        for w, target in zip(root_weights, output):
            for i, x in enumerate(vector):
                for j, y in enumerate(vector):
                    target[i*size+j] += w*x*y
    return [Q(x, 2*mass*degree**2) for row in output for x in row]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("cache", type=Path)
    parser.add_argument("orientation", type=Path)
    parser.add_argument("--vendor", type=Path)
    args = parser.parse_args()
    if args.vendor:
        sys.path.insert(0, str(args.vendor))

    import numpy as np
    from scipy.sparse import save_npz

    data = dict(np.load(args.cache.with_suffix(".data.npz")))
    oriented = dict(np.load(args.orientation.with_suffix(".data.npz")))
    matrix, size = build(data, oriented)
    save_npz(args.orientation.with_suffix(".gram.npz"), matrix)
    print(json.dumps({"shape": matrix.shape, "nnz": matrix.nnz, "blocks": [size,size]}))


if __name__ == "__main__":
    main()
