"""Separate and replay exact projected constraints for the oriented extra-support model."""

import argparse
from collections import defaultdict
from fractions import Fraction as Q
import hashlib
import json
from math import lcm
from pathlib import Path
import sys


SUFFIXES = (".data.npz", ".degree.npz", ".split.npz", ".sample.npz", ".sample_tag.npz")
OUTPUT_SCALE = 10**6


def hashes(path):
    return {s: hashlib.sha256(path.with_suffix(s).read_bytes()).hexdigest() for s in SUFFIXES}


def load(path, bounds):
    import numpy as np
    from scipy.sparse import coo_matrix, load_npz, vstack

    data = dict(np.load(path.with_suffix(".data.npz")))
    degree, split, sample, tagged = [
        load_npz(path.with_suffix(f".{name}.npz")).astype(np.int64)
        for name in ("degree", "split", "sample", "sample_tag")
    ]
    used = data["sample_parent"]
    aut = data["aut"][used]
    parents = coo_matrix((aut, (np.arange(len(used)), used)), shape=sample.shape).tocsr()
    lo, hi, el, eh = map(Q, bounds)
    assert 0 < lo <= hi and 0 <= el <= eh <= 1
    scale = lcm(lo.denominator, hi.denominator, el.denominator, eh.denominator)
    s = int(scale)
    inequality = vstack((
        int(2*lo*s)*parents-s*sample, s*sample-int(2*hi*s)*parents,
        int(el*s)*sample-s*tagged, s*tagged-int(eh*s)*sample,
    ), format="csr")
    return data, split.tocsr(), degree.tocsr(), inequality, s


def propose(system, x, aut, seconds):
    import numpy as np
    from scipy.optimize import linprog
    from scipy.sparse import csr_matrix, hstack, vstack

    _, split, degree, inequality, scale = system
    n = split.shape[0]
    w = csr_matrix((1/aut).reshape(-1, 1))
    A = vstack((hstack((split, -w)), hstack((-split, -w)),
                hstack((inequality/scale, csr_matrix((inequality.shape[0], 1))))), format="csr")
    b = np.r_[x, -x, np.zeros(inequality.shape[0])]
    E = hstack((degree, csr_matrix((degree.shape[0], 1))), format="csr")
    c = np.r_[np.zeros(A.shape[1]-1), 1.]
    result = linprog(c, A_ub=A, b_ub=b, A_eq=E, b_eq=np.zeros(E.shape[0]), bounds=(0., None),
                     method="highs-ipm", options={"time_limit": seconds})
    if not result.success:
        raise RuntimeError(result.message)
    den = 10**10
    rows = result.ineqlin.marginals
    shadow = rows[:n]-rows[n:2*n]

    def sparse(vals, nonpositive):
        yield from ((i, q) for i, v in enumerate(vals)
                    if (q := min(0, round(v*den)) if nonpositive else round(v*den)))

    return {"value": float(result.fun), "shadow": list(sparse(shadow, False)),
            "equality": list(sparse(result.eqlin.marginals, False)),
            "inequality": list(sparse(rows[2*n:], True))}


def replay(system, proof, absolute_limit=None):
    from scipy.sparse import csr_matrix
    import numpy as np

    data, split, degree, inequality, scale = system
    n, n_lift = split.shape
    shadow = dict(proof["shadow"])
    assert len(shadow) == len(proof["shadow"])
    assert all(0 <= i < n and type(v) is int for i, v in shadow.items())
    owner = data["owner"]
    residual = [shadow.get(int(i), 0)*scale for i in owner]

    def accumulate(matrix, entries, scale_factor, nonpositive):
        seen = set()
        for row, multiplier in entries:
            assert 0 <= row < matrix.shape[0] and type(multiplier) is int and row not in seen
            assert not nonpositive or multiplier <= 0
            seen.add(row)
            first, last = matrix.indptr[row:row+2]
            for c, value in zip(matrix.indices[first:last], matrix.data[first:last]):
                residual[c] += int(value)*multiplier*scale_factor

    accumulate(degree, proof["equality"], scale, False)
    accumulate(inequality, proof["inequality"], 1, True)
    errors = defaultdict(int)
    for i, r in zip(map(int, owner), residual):
        if r > errors[i]:
            errors[i] = r
    corrected = {i: shadow.get(i, 0)*scale-errors.get(i, 0) for i in set(shadow)|set(errors)}
    divisor = max(map(abs, corrected.values()), default=0)
    if not divisor:
        raise ValueError("Zero projected constraint")
    if absolute_limit:
        divisor = max(divisor, absolute_limit)
    cut = [(i, value*OUTPUT_SCALE//divisor) for i, value in sorted(corrected.items()) if value]
    where = np.asarray([i for i, _ in cut], dtype=np.intp)
    what = np.asarray([v for _, v in cut], dtype=np.int64)
    return csr_matrix((what, (np.zeros(len(cut), dtype=np.intp), where)), shape=(1, n))


def replay_file(path, settings):
    from scipy.sparse import vstack

    record = json.loads(path.read_bytes())
    source = path.parent/record["source"]
    assert hashes(source) == record["hashes"]
    demands = [Q(settings[key]) for key in ("mass_low", "mass_high", "e_low", "e_high")]
    actual = list(map(Q, record["bounds"]))
    assert actual[0] <= demands[0] <= demands[1] <= actual[1]
    assert actual[2] <= demands[2] <= demands[3] <= actual[3]
    system = load(source, actual)
    return vstack([replay(system, proof) for proof in record["cuts"]], format="csr")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("cache", type=Path)
    parser.add_argument("source", type=Path)
    parser.add_argument("record", type=Path)
    parser.add_argument("point", nargs="+", type=Path)
    parser.add_argument("--vendor", type=Path)
    parser.add_argument("--bounds", nargs=4, default=["5/4", "2579/2000", "0", "3/8"])
    parser.add_argument("--seconds", type=int, default=180)
    parser.add_argument("--accept", type=float, default=1e-5)
    args = parser.parse_args()
    if args.vendor:
        sys.path.insert(0, str(args.vendor))

    import numpy as np

    data = np.load(args.cache.with_suffix(".data.npz"))
    aut = data["aut_count"]
    system = load(args.source, args.bounds)
    files = hashes(args.source)
    if args.record.exists():
        record = json.loads(args.record.read_bytes())
        assert record["hashes"] == files and list(map(Q, record["bounds"])) == list(map(Q, args.bounds))
    else:
        assert args.source.parent.resolve() == args.record.parent.resolve()
        record = {"source": args.source.name, "hashes": files, "bounds": args.bounds, "cuts": []}
    for p in args.point:
        point = np.maximum(np.load(p)["x"], 0)
        proof = propose(system, point, aut, args.seconds)
        candidate = replay(system, proof)
        value = float((candidate@point)[0])/OUTPUT_SCALE
        print(json.dumps({"point": str(p), "distance": proof["value"],
                          "exact_row_at_point": value, "nnz": candidate.nnz}), flush=True)
        if value > args.accept and np.max(candidate.data, initial=0) > 0:
            record["cuts"].append(proof)
            args.record.write_text(json.dumps(record, separators=(",", ":"))+"\n", encoding="utf-8")


if __name__ == "__main__":
    main()
