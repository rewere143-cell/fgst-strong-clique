"""Check exact degree-mixed rows against direct computations on weighted hosts."""

import argparse
from fractions import Fraction as Q
import json
from pathlib import Path
import sys

from audit_multigraph_type_forest_psd import direct_maps, tag_weight
from multigraph_blend_moments import degree_moment_rows


def verify(data, colors, extra):
    from math import lcm
    import numpy as np

    h = [row.count(2) for row in colors]
    blue = [row.count(1) for row in colors]
    j = [sum(row) for row in extra]
    degree = [u+v+w for u, v, w in zip(h, blue, j)]
    assert len(set(degree)) == 1
    D = degree[0]
    s, R = sum(h)//2, sum(j)//2
    m = s+R
    M = Q(m, D**2)
    low, high = Q(1), Q(3, 2)
    rows, grams = degree_moment_rows(data, low, high)
    normalization = lcm(*map(int, data["aut_count"]))*2*m*D**2
    maps = {n: direct_maps(colors, n) for n in range(2, 5)}
    values = np.zeros(len(data["order"]), dtype=np.int64)
    for i, (n, c, mask, aut) in enumerate(zip(data["order"], data["code"], data["mask"], data["aut_count"])):
        if n <= 4:
            total = sum(tag_weight(extra, joint, mask) for joint in maps[n].get(c, ()))
            values[i] = total*normalization//(int(aut)*2*m*D**(int(n)-2))
    first, second, third = [Q(sum(x**k for x in j), 2*m*D**(k-1)) for k in (1, 2, 3)]
    pair_scale = 2*m*D**2
    cross = [range(len(h))]*2
    positive = [(u, v) for u in cross[0] for v in cross[1] if colors[u][v]]
    bridge = Q(sum(j[u]*j[v] for u, v in positive), pair_scale)
    mixed = Q(sum(j[u]*h[v] for u, v in positive), pair_scale)
    buffer = Q(sum(j[u]*blue[v] for u, v in positive), pair_scale)
    extra_mass = Q(R*R, m*D**2)
    product = Q(s*R, m*D**2)
    expected = [
        extra_mass-2*bridge,
        product-2*mixed,
        bridge+third-second,
        2*second+2*buffer+extra_mass+product-2*first,
    ]
    for t in (low, (low+high)/2, high):
        expected.append(t*M-t*t/2-Q(s, D**2))
    # The objective uses exactly four positions; its complete numerator is in values.
    observed = [
        sum(Q(c)*Q(int((a@values)[0]), normalization) for c, a in row)
        for row in rows
    ]
    assert observed == expected, (observed, expected)
    assert all(x <= 0 for x in expected[:4])
    if M >= 1:
        assert all(x <= 0 for x in expected[4:])
    for c, (matrix, size) in enumerate(grams, 1):
        found = [Q(int(x), normalization) for x in matrix.T@values]
        if c == 3:
            assert size == 2 and found == [first, second, second, third]
        else:
            assert size == 4
            target = [0]*16
            for u, v in positive:
                if colors[u][v] != c:
                    continue
                w = [h[u], j[u], h[v], j[v]]
                for i in range(4):
                    for k in range(4):
                        target[i*4+k] += w[i]*w[k]
            assert found == [Q(x, pair_scale) for x in target]
    return {"vertices": len(h), "degree": D, "marked": m, "extra": R,
            "inequalities": len(rows), "gram_entries": sum(size**2 for _, size in grams)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("cache", type=Path)
    parser.add_argument("--vendor", type=Path)
    args = parser.parse_args()
    if args.vendor:
        sys.path.insert(0, str(args.vendor))

    import numpy as np

    data = dict(np.load(args.cache.with_suffix(".data.npz")))
    assert data["max_degree"]
    C5 = [[2*int((x-y) % 5 in (1, 4)) for y in range(5)] for x in range(5)]
    C4 = [[0, 2, 1, 2], [2, 0, 2, 1], [1, 2, 0, 2], [2, 1, 2, 0]]
    inputs = [
        ([[0, 2], [2, 0]], [[0, 1], [1, 0]]),
        (C4, [[0, 1, 0, 2], [1, 0, 2, 0], [0, 2, 0, 1], [2, 0, 1, 0]]),
        (C5, [[int(c == 2) for c in row] for row in C5]),
        (C5, [[0]*5 for _ in range(5)]),
    ]
    print(json.dumps([verify(data, colors, extra) for colors, extra in inputs]))


if __name__ == "__main__":
    main()
