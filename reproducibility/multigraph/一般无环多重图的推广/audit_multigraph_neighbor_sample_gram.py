"""Check neighbor-sampling Gram matrices by direct weighted draws."""

import argparse
from fractions import Fraction as Q
from itertools import product
import json
from math import lcm
from pathlib import Path
import sys

from audit_multigraph_oriented_forest import fixtures
from audit_multigraph_type_forest_psd import direct_maps, tag_weight
from multigraph_lift_probe import edge_pairs
from multigraph_neighbor_sample_gram import SAMPLE_EDGES, SIZE, blocks
from multigraph_sample_gram import neighbors


def verify(cache, data, colors, extra):
    import numpy as np

    host = range(len(colors))
    w = [[int(c > 0)+b for c, b in zip(row, tags)] for row, tags in zip(colors, extra)]
    D = sum(w[0])
    assert all(sum(row) == D for row in w)
    red = [(x, y) for x, y in product(host, repeat=2) if colors[x][y] == 2]
    m = sum(w[x][y] for x, y in red)//2
    maps = {n: direct_maps(colors, n) for n in range(2, 6)}
    denom = lcm(*map(int, data["aut_count"]))*2*m*D**3
    x = []
    for n, code, mask, aut in zip(data["order"], data["code"], data["mask"], data["aut_count"]):
        total = sum(tag_weight(extra, im, mask) for im in maps[n].get(code, ()))
        x.append(denom*total//(int(aut)*2*m*D**(int(n)-2)))
    x = np.asarray(x, dtype=np.int64)
    report = 0
    for part, (matrix, order) in enumerate(blocks(cache, 1, range(4))):
        layout, root_tag = divmod(part, 2)
        edges = SAMPLE_EDGES[layout]
        tail = [edge for edge in edge_pairs(4) if edge not in set(edges)|{(0, 1)}]
        features = [flag for flag in neighbors() if not root_tag or flag[-1] < 0]
        expect = [Q(0)]*(order**2)
        assert order == SIZE+len(features)
        for u, v in red:
            weight = Q(extra[u][v] if root_tag else 1, 2*m)
            if not weight:
                continue
            f = []
            for a, b, at in features:
                total = sum((1 if at < 0 else extra[(u, v)[at]][z]) for z in host
                            if colors[u][z] == a and colors[v][z] == b)
                f.append(Q(total, D))
            sample = [Q(0)]*SIZE
            for s, t in product(host, repeat=2):
                im = (u, v, s, t)
                product_weight = 1
                for i, j in edges:
                    product_weight *= w[im[i]][im[j]]
                signature = sum(colors[im[i]][im[j]]*3**k for k, (i, j) in enumerate(tail))
                sample[signature] += Q(product_weight, D**2)
            assert sum(sample) == 1
            for i, g in enumerate(f):
                for j, h in enumerate(f):
                    expect[i*order+j] += weight*g*h
                for j, h in enumerate(sample, len(f)):
                    expect[i*order+j] += weight*g*h
                    expect[j*order+i] += weight*g*h
            for j, h in enumerate(sample, len(f)):
                expect[j*order+j] += weight*h
        got = [Q(int(a), denom) for a in matrix.T@x]
        assert got == expect
        report += order**2
    return {"vertices": len(host), "degree": D, "marked": m, "entries": report}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("cache", type=Path)
    p.add_argument("--vendor", type=Path)
    args = p.parse_args()
    if args.vendor:
        sys.path.insert(0, str(args.vendor))

    import numpy as np

    data = dict(np.load(args.cache.with_suffix(".data.npz")))
    print(json.dumps([verify(args.cache, data, colors, extra) for colors, extra, _ in fixtures()]))


if __name__ == "__main__":
    main()
