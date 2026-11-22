"""Check oriented forest contractions and test a relaxed point for an orientation lift."""

import argparse
from fractions import Fraction as Q
import json
from math import lcm
from pathlib import Path
import sys

from audit_multigraph_type_forest_psd import direct_maps, tag_weight
from multigraph_lift_probe import edge_pairs


def check(data, lifted, matrix, colors, extra, direction):
    import numpy as np

    projection, degree, sample, tagged, *extra_grams = matrix
    arity = lifted["arity"]
    order = int(max(arity))
    D = [sum(c > 0 for c in row)+sum(e) for row, e in zip(colors, extra)]
    assert len(set(D)) == 1
    D = int(D[0])
    s = sum(row.count(2) for row in colors)//2
    R = sum(map(sum, extra))//2
    m = s+R
    maps = [None, None]+[direct_maps(colors, n) for n in range(2, order+1)]
    scale = lcm(*map(int, data["aut_count"]), *map(int, lifted["aut"]))*2*m*D**(order-2)
    expected_unoriented = np.zeros(len(data["order"]), dtype=np.int64)
    for i, (n, code, mask, aut) in enumerate(zip(data["order"], data["code"], data["mask"], data["aut_count"])):
        if n <= order:
            total = sum(tag_weight(extra, im, mask) for im in maps[n].get(code, ()))
            expected_unoriented[i] = total*scale//(int(aut)*2*m*D**(int(n)-2))
    values = []
    for idx, d, a in zip(lifted["owner"], lifted["reverse"], lifted["aut"]):
        n, code, mask = [int(data[k][idx]) for k in ("order", "code", "mask")]
        pairs = [(v, u) if (d >> e) & 1 else (u, v) for e, (u, v) in enumerate(edge_pairs(n))
                 if (mask >> e) & 1]
        total = sum(tag_weight(extra, im, mask) for im in maps[n].get(code, ())
                    if all((im[u], im[v]) in direction for u, v in pairs))
        values.append(total*scale//(a*2*m*D**(n-2)))
    values = np.asarray(values, dtype=np.int64)
    assert np.array_equal(projection@values, expected_unoriented)
    if np.any(degree@values):
        hits = np.flatnonzero(degree@values)
        examples = []
        for row in hits[:10]:
            ind = degree.indices[degree.indptr[row]:degree.indptr[row+1]]
            nz = [int(i) for i in ind if values[i]]
            examples.append((int(row), int((degree@values)[row]), [
                (int(i), int(lifted["owner"][i]), int(lifted["reverse"][i]), int(values[i]),
                 int(degree[row, i]), int(lifted["row_diagonal"][i])) for i in nz]))
        raise AssertionError((len(colors), len(hits), examples))
    use = lifted["sample_parent"]
    assert np.array_equal(D*D*(sample@values), 2*m*lifted["aut"][use]*values[use])
    assert np.array_equal(D*D*(tagged@values), 2*R*lifted["aut"][use]*values[use])
    if extra_grams:
        from multigraph_oriented_gram import direct

        gram, = extra_grams
        found = [Q(int(x), scale) for x in gram.T@values]
        assert found == direct(colors, extra, direction)
    return {"n": len(colors), "D": D, "m": m, "R": R, "atoms": len(values),
            "degree": degree.shape[0], "sample": sample.shape[0]}


def fixtures():
    yield [[0, 2], [2, 0]], [[0, 1], [1, 0]], {(0, 1)}
    yield [[0, 2, 2], [2, 0, 2], [2, 2, 0]], [[0, 1, 1], [1, 0, 1], [1, 1, 0]], {(0, 1), (1, 2), (2, 0)}
    size = 8
    colors = [[0]*size for _ in range(size)]
    extra = [[0]*size for _ in range(size)]
    for v in (1, 2):
        colors[0][v] = colors[v][0] = 2
        extra[0][v] = extra[v][0] = 1
    for v, u in [(1, 2), (1, 3), (2, 4)]+[(i, j) for i in range(3, 8) for j in range(3, i) if (j, i) != (3, 4)]:
        colors[v][u] = colors[u][v] = 1
    yield colors, extra, {(1, 0), (2, 0)}


def closest(data, lifted, matrix, point_path, seconds, slack):
    import numpy as np
    from scipy.optimize import linprog
    from scipy.sparse import csr_matrix, hstack, vstack, coo_matrix

    split, degree, sample, tagged = matrix[:4]
    x = np.load(point_path)["x"]
    assert len(x) == split.shape[0]
    ar = data["aut_count"]
    w = csr_matrix((1/ar).reshape(-1, 1))
    x = x.copy()
    x[split.getnnz(1) == 0] = 0
    low, high = data["twice_obj"] @ x/2-slack, data["twice_obj"] @ x/2+slack
    root = (data["order"] == 2) & (data["mask"] != 0)
    share = (ar*root) @ x
    l, h = max(0., share-slack), min(1., share+slack)
    used = lifted["sample_parent"]
    attach = coo_matrix((lifted["aut"][used], (np.arange(len(used)), used)), shape=sample.shape).tocsr()
    rest = vstack((2*low*attach-sample, sample-2*high*attach, l*sample-tagged,
                   tagged-h*sample), format="csr")
    A = vstack((hstack((split, -w)), hstack((-split, -w)),
                hstack((rest, csr_matrix((rest.shape[0], 1))))), format="csr")
    b = np.r_[x, -x, np.zeros(rest.shape[0])]
    E = hstack((degree, csr_matrix((degree.shape[0], 1))), format="csr")
    c = np.r_[np.zeros(A.shape[1]-1), 1.]
    r = linprog(c, A_ub=A, b_ub=b, A_eq=E, b_eq=np.zeros(E.shape[0]), bounds=(0., None),
                method="highs-ipm", options={"time_limit": seconds})
    result = {"point": str(point_path), "status": r.message, "mass": (low, high),
              "share": (l, h), "minimax_error": r.fun}
    if r.success:
        indices = np.argsort(abs(r.ineqlin.marginals))[-8:][::-1]
        result["largest_marginals"] = [(int(i), float(r.ineqlin.marginals[i])) for i in indices]
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    parser.add_argument("lift", type=Path)
    parser.add_argument("--vendor", type=Path)
    parser.add_argument("--point", nargs="+", type=Path)
    parser.add_argument("--seconds", type=int, default=180)
    parser.add_argument("--slack", type=float, default=.001)
    args = parser.parse_args()
    if args.vendor:
        sys.path.insert(0, str(args.vendor))
    import numpy as np
    from scipy.sparse import load_npz

    data = dict(np.load(args.input.with_suffix(".data.npz")))
    lifted = dict(np.load(args.lift.with_suffix(".data.npz")))
    matrix = [load_npz(args.lift.with_suffix(f".{x}.npz"))
              for x in ("split", "degree", "sample", "sample_tag")]
    gram = args.lift.with_suffix(".gram.npz")
    if gram.exists():
        matrix.append(load_npz(gram))
    if args.point:
        for point in args.point:
            print(json.dumps(closest(data, lifted, matrix, point, args.seconds, args.slack)), flush=True)
    else:
        print(json.dumps([check(data, lifted, matrix, *host) for host in fixtures()]))


if __name__ == "__main__":
    main()
