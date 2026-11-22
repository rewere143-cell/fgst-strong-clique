"""Three-color categorical Gram matrices for two-step degree-neighbor samples."""

import argparse
from array import array
import hashlib
import json
from pathlib import Path
import sys
from time import monotonic

from multigraph_lift_probe import decode, edge_pairs
from multigraph_sample_gram import neighbors
from multigraph_weighted_ore_model import permutation_slots


SAMPLE_EDGES = (((0, 2), (1, 3)), ((0, 2), (2, 3)))
SIZE = 27


def raw(cache):
    import numpy as np
    from scipy.sparse import coo_matrix, save_npz

    started = monotonic()
    data = dict(np.load(cache.with_suffix(".data.npz")))
    all_features = {x: i for i, x in enumerate(neighbors())}
    f = len(all_features)
    lists = [(array("i"), array("i")) for _ in range(2)]
    for n in (4, 5):
        es = edge_pairs(n)
        slots = {edge: i for i, edge in enumerate(es)}
        p = np.asarray(permutation_slots(n), dtype=np.int64)
        root = slots[0, 1]
        used = [[slots[e] for e in path] for path in SAMPLE_EDGES]
        others = [[slots[e] for e in edge_pairs(4) if e not in set(path)|{(0, 1)}]
                  for path in SAMPLE_EDGES]
        for row in np.flatnonzero(data["order"] == n):
            colors = np.asarray(decode(n, int(data["code"][row])))[p]
            dec = (int(data["mask"][row]) >> p)&1
            valid = np.flatnonzero(colors[:, root] == 2)
            for k in valid:
                c, t = colors[k], dec[k]
                tag = int(t[root])
                dec_count = int(t.sum())
                feature = -1
                other_tag = 0
                if n == 5:
                    x, y = slots[0, 4], slots[1, 4]
                    if not (c[x] or c[y]):
                        continue
                    other_tag = int(t[x]+t[y])
                    if other_tag > 1 or (tag and other_tag):
                        continue
                    target = 0 if t[x] else 1 if t[y] else -1
                    feature = all_features[int(c[x]), int(c[y]), target]
                for layout, (edge, tail) in enumerate(zip(used, others)):
                    u, v = edge
                    if not (c[u] and c[v]) or dec_count != tag+t[u]+t[v]+other_tag:
                        continue
                    part = layout*2+tag
                    bin_index = sum(int(c[e])*3**i for i, e in enumerate(tail))
                    rows, cols = lists[n-4]
                    rows.append(row)
                    cols.append(part*SIZE+bin_index if n == 4 else part*f*SIZE+feature*SIZE+bin_index)
    report = {}
    for name, (rows, cols), dim in zip(("mass", "cross"), lists, (4*SIZE, 4*f*SIZE)):
        matrix = coo_matrix((np.ones(len(rows), dtype=np.int64), (rows, cols)),
                            shape=(len(data["order"]), dim)).tocsr()
        save_npz(cache.with_suffix(f".neighbor_{name}.npz"), matrix)
        report[name] = matrix.nnz
    print(json.dumps({"nnz": report, "seconds": monotonic()-started}))


def hashes(cache):
    return {name: hashlib.sha256(cache.with_suffix(f".{name}.npz").read_bytes()).hexdigest()
            for name in ("sample_covariance", "neighbor_mass", "neighbor_cross")}


def blocks(cache, scale, include):
    import numpy as np
    from scipy.sparse import csr_matrix, hstack, load_npz

    flags = neighbors()
    f = len(flags)
    cov, mass, crossing = [
        load_npz(cache.with_suffix(f".{name}.npz")).tocsc().astype(np.int64)
        for name in ("sample_covariance", "neighbor_mass", "neighbor_cross")
    ]
    n = cov.shape[0]
    zero = csr_matrix((n, 1), dtype=np.int64)
    for part in sorted(set(include)):
        root_tag = part % 2
        keep = [i for i, flag in enumerate(flags) if not root_tag or flag[-1] < 0]
        diag = mass[:, part*SIZE:(part+1)*SIZE]
        categories = np.flatnonzero(diag.getnnz(axis=0))
        inverse = {int(a): i+len(keep) for i, a in enumerate(categories)}
        at = {}
        for a, i in enumerate(keep):
            for b, j in enumerate(keep):
                at[a, b] = cov[:, root_tag*f*f+i*f+j]*scale
            for cat, b in inverse.items():
                at[a, b] = at[b, a] = crossing[:, (part*f+i)*SIZE+cat]*scale
        for cat, b in inverse.items():
            at[b, b] = diag[:, cat]*scale
        size = len(keep)+len(categories)
        yield hstack([at.get((i, j), zero) for i in range(size) for j in range(size)], format="csc"), size


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("cache", type=Path)
    parser.add_argument("--vendor", type=Path)
    args = parser.parse_args()
    if args.vendor:
        sys.path.insert(0, str(args.vendor))
    raw(args.cache)


if __name__ == "__main__":
    main()
