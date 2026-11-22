"""Independently check the categorical sample matrices on small weighted hosts."""

import argparse
from fractions import Fraction as Q
from itertools import product
import json
from math import lcm
from pathlib import Path
import sys

from audit_multigraph_oriented_forest import fixtures
from audit_multigraph_type_forest_psd import direct_maps, tag_weight
from multigraph_sample_gram import categories, model_blocks, neighbors


def verify(cache, data, colors, extra, local=False):
    import numpy as np

    n = len(colors)
    host = range(n)
    red = [(u, v) for u, v in product(host, repeat=2) if colors[u][v] == 2]
    s = len(red)//2
    R = sum(extra[u][v] for u, v in red)//2
    m = s+R
    D = sum(c > 0 for c in colors[0])+sum(extra[0])
    assert all(sum(c > 0 for c in row)+sum(b) == D for row, b in zip(colors, extra))
    labels = neighbors()
    bins = {x: i for i, x in enumerate(categories())}
    f, h = len(labels), len(bins)
    size = f+1+h
    maps = {k: direct_maps(colors, k) for k in range(2, 6)}
    density_scale = lcm(*map(int, data["aut_count"]))*2*m*D**3
    density = []
    for k, c, aut, mask in zip(data["order"], data["code"], data["aut_count"], data["mask"]):
        value = sum(tag_weight(extra, image, mask) for image in maps[k].get(c, ()))
        density.append(value*density_scale//(2*m*D**(int(k)-2)*int(aut)))
    density = np.asarray(density, dtype=np.int64)
    bounds = (Q(s, D*D)+Q(1, 17), Q(R, D*D)+Q(1, 13))
    scale = lcm(*(x.denominator for x in bounds))
    blocks = model_blocks(cache, bounds, scale)
    expected = [[Q(0)]*(size*size) for _ in blocks]
    for x, y in red:
        feature = [Q(1)]
        for a, b, at in labels:
            use = ((x if at == 0 else y) if at >= 0 else -1)
            count = sum((1 if use < 0 else extra[use][w]) for w in host
                        if colors[x][w] == a and colors[y][w] == b)
            feature.append(Q(count, D))
        for part, dest in enumerate(expected):
            root_tag, target_tag = divmod(part, 2)
            weight = Q(extra[x][y] if root_tag else 1, 2*m)
            if not weight:
                continue
            sample = [Q(0)]*h
            for u, v in red:
                signatures = tuple(sorted(colors[x][w]+3*colors[y][w] for w in (u, v)))
                bin_index = bins[signatures]
                sample[bin_index] += Q(extra[u][v] if target_tag else 1, D*D)
            total = sum(sample)
            assert total == Q(2*(R if target_tag else s), D*D)
            for i, a in enumerate(feature):
                for j, b in enumerate(feature):
                    dest[i*size+j] += weight*a*b*(2*bounds[target_tag] if i and j else total)
                for j, b in enumerate(sample, f+1):
                    dest[i*size+j] += weight*a*b
                    dest[j*size+i] += weight*a*b
            for j, value in enumerate(sample, f+1):
                dest[j*size+j] += weight*value
    for (block, count), want in zip(blocks, expected):
        assert count == size
        got = [Q(int(x), scale*density_scale) for x in block.T@density]
        assert got == want
    extra_entries = verify_local(cache, density, density_scale, colors, extra, D, m) if local else 0
    return {"vertices": n, "degree": D, "marked": m, "extra": R,
            "matrices": 4, "entries": 4*size**2, "local_entries": extra_entries}



def verify_local(cache, values, density_scale, colors, extra, degree, marked):
    from scipy.sparse import load_npz
    from multigraph_local_sample_psd import blocks

    n = len(colors)
    roots = [(u, v) for u, v in product(range(n), repeat=2) if colors[u][v] == 2]
    labels = neighbors()
    dimension = len(labels)
    coefficients = [
        load_npz(cache.with_suffix(f".{suffix}.npz"))
        for suffix in ("sample_covariance", "ore_sample_qcov", "ore_sample_supportcov")
    ]
    expected = [[[Q(0)]*(dimension**2) for _ in range(2)] for _ in coefficients]
    size = dimension+2
    local = [[Q(0)]*(size**2) for _ in range(4)]
    for u, v in roots:
        h = [Q(sum((1 if at < 0 else extra[(u, v)[at]][z]) for z in range(n)
                   if colors[u][z] == a and colors[v][z] == b), degree)
             for a, b, at in labels]
        red = Q(colors[v].count(2), degree)
        support = Q(sum(c > 0 for c in colors[v]), degree)
        for p, out in enumerate(expected):
            for r in (0, 1):
                w = Q(extra[u][v] if r else 1, 2*marked)*(1, red, support)[p]
                for i, a in enumerate(h):
                    for j, b in enumerate(h):
                        out[r][i*dimension+j] += w*a*b
        for part, out in enumerate(local):
            r, t = divmod(part, 2)
            w = Q(extra[u][v] if r else 1, 2*marked)
            if not w:
                continue
            beta = Q(1, 4) if t else Q(273323, 10**6)
            f = [Q(0), Q(0)]
            for x, y in roots:
                if colors[u][x] and not colors[v][x] and not colors[u][y] and not colors[v][y]:
                    f[colors[u][x]-1] += Q(2*(extra[x][y] if t else 1), degree**2)
            bound = 2*beta*(4-3*red)
            assert sum(f) <= bound
            for i, a in enumerate(h):
                for j, b in enumerate(h):
                    out[i*size+j] += w*bound*a*b
                for j, b in enumerate(f, dimension):
                    out[i*size+j] += w*a*b
                    out[j*size+i] += w*a*b
            for j, b in enumerate(f, dimension):
                out[j*size+j] += w*b
    for matrix, group in zip(coefficients, expected):
        found = [Q(int(x), density_scale) for x in matrix.T@values]
        assert found == group[0]+group[1]
    scale = 500000
    for (matrix, count), group in zip(blocks(cache, scale, range(4)), local):
        assert count == size
        assert [Q(int(x), scale*density_scale) for x in matrix.T@values] == group
    return len(coefficients)*2*dimension**2+4*size**2


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("cache", type=Path)
    parser.add_argument("--vendor", type=Path)
    parser.add_argument("--local", action="store_true")
    args = parser.parse_args()
    if args.vendor:
        sys.path.insert(0, str(args.vendor))

    import numpy as np

    info = dict(np.load(args.cache.with_suffix(".data.npz")))
    examples = [(colors, extra) for colors, extra, _ in fixtures()]
    pentagon = [[2*int((u-v)%5 in (1, 4)) for v in range(5)] for u in range(5)]
    examples.append((pentagon, [[int(c == 2) for c in row] for row in pentagon]))
    print(json.dumps([verify(args.cache, info, *x, args.local) for x in examples]))


if __name__ == "__main__":
    main()
