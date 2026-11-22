"""Verify anchored-cycle inequalities using exact integers and audited flag exports.

The input stores only scalar weights. The original compact certificate supplies
rank-one vectors, already indexed in the independent reverse-projection basis.
No numerical optimizer or nonstandard Python module is used.
"""
import argparse
from array import array
from fractions import Fraction
from hashlib import sha256
from itertools import combinations, product
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
DATA = HERE / "source_snapshot/reproducibility/data"
BASE = DATA / "compact_certificate.json"
BASE_HASH = "369542796834aa1f297dccf750f1743c8f01827d8b4ef08ef044ff474909a912"
CYCLE = {(0, 1), (1, 2), (2, 3), (3, 4), (0, 4)}
CONDITIONAL_RHO = Fraction(34, 125)


def exact_integer(value):
    if type(value) is int:
        return value
    if type(value) is str and re.fullmatch(r"[+-]?[0-9]+", value):
        return int(value)
    raise TypeError(f"Expected an exact integer: {value!r}")


def unique_object(items):
    result = {}
    for key, value in items:
        if key in result:
            raise ValueError(f"Duplicate JSON key: {key}")
        result[key] = value
    return result


def load_json(path):
    return json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=unique_object)


def read_array(path, kind):
    result = array(kind)
    assert result.itemsize == {"i": 4, "q": 8}[kind]
    nbytes = path.stat().st_size
    assert nbytes % result.itemsize == 0
    with path.open("rb") as stream:
        result.fromfile(stream, nbytes // result.itemsize)
    if sys.byteorder != "little":
        result.byteswap()
    return result


def colors(n, code):
    result = [2]
    for _ in range(n * (n - 1) // 2 - 1):
        code, color = divmod(code, 3)
        result.append(color)
    assert code == 0
    return tuple(result)


def degree_row_names(data):
    lines = (data / "degree.txt").read_text().splitlines()
    rows = [tuple(map(int, line.split())) for line in lines[1:]]
    assert len(rows) == int(lines[0])
    names = [f"degree_{k}_{colors(k, code)}_{u}" for k, code, u in rows]
    assert len(names) == len(set(names))
    return rows, names


def cycle_expression(mode, nvars, ratio=CONDITIONAL_RHO):
    """Return coefficients for the signed expression added to the sharp objective."""
    idx5 = read_array(DATA / "idx5.bin", "i")
    assert len(idx5) == 3**9 and max(idx5) == 727
    pairs5 = list(combinations(range(5), 2))
    code5 = sum(2 * 3**p for p, pair in enumerate(pairs5[1:]) if pair in CYCLE)
    q_cycle = idx5[code5]
    assert 0 <= q_cycle < 728
    if mode == "abundance":
        return q_cycle, {q_cycle: -1}
    assert mode in {"anchor", "conditional"}
    idx6 = read_array(DATA / "order6_orbit_index.bin", "i")
    assert len(idx6) == 3**14 and 728 + max(idx6) == nvars - 1
    pairs6 = list(combinations(range(6), 2))
    coefficients = {}
    for extension in product(range(3), repeat=5):
        ind = any(extension[i] and extension[j] for i, j in CYCLE)
        if 1 not in extension and not ind:
            continue
        code = 0
        for p, (i, j) in enumerate(pairs6[1:]):
            color = extension[i] if j == 5 else 2 * ((i, j) in CYCLE)
            code += color * 3**p
        orbit = idx6[code]
        if orbit >= 0:
            position = 728 + orbit
            coefficients[position] = coefficients.get(position, 0) + sum(
                color != 0 for color in extension
            )
    if mode == "conditional":
        coefficients = {i: c * ratio.denominator for i, c in coefficients.items()}
        coefficients[q_cycle] = -ratio.numerator
    return q_cycle, coefficients


def read_sparse(keys_path, values_path, rows, cols):
    keys = read_array(keys_path, "q")
    values = read_array(values_path, "i")
    assert len(keys) == len(values) and keys
    assert keys[0] >= 0 and keys[-1] < rows * cols
    assert all(x < y for x, y in zip(keys, keys[1:]))
    return keys, values


def red_triangle_coordinates():
    """The archived coordinate indices forced to vanish for triangle-free marks."""
    views = ((3, "idx3.bin", 0), (4, "idx4.bin", 0), (5, "idx5.bin", 0),
             (6, "order6_orbit_index.bin", 728))
    excluded = set()
    for order, filename, offset in views:
        pairs = tuple(combinations(range(order), 2))
        indexed = {pair: 3**i for i, pair in enumerate(pairs[1:])}
        orbit = read_array(DATA / filename, "i")
        assert len(orbit) == 3**len(indexed)
        for triple in combinations(range(order), 3):
            fixed = set(combinations(triple, 2))
            start = sum(2 * value for pair, value in indexed.items() if pair in fixed)
            codes = [start]
            for pair, value in indexed.items():
                if pair not in fixed:
                    codes = [code + digit * value for code in codes for digit in range(3)]
            excluded.update(offset + orbit[code] for code in codes if orbit[code] >= 0)
    return excluded


def verify(candidate_path, *, triangle_free=False, max_error=Fraction(1, 10**6)):
    assert sha256(BASE.read_bytes()).hexdigest() == BASE_HASH
    base = load_json(BASE)
    candidate = load_json(candidate_path)
    assert candidate["source_rank_one_vectors_sha256"] == BASE_HASH
    mode = candidate["mode"]
    assert mode in {"abundance", "anchor", "conditional"}
    ratio = CONDITIONAL_RHO
    if mode == "conditional" and "anchor_ratio" in candidate:
        encoded = candidate["anchor_ratio"]
        assert type(encoded) is str
        ratio = Fraction(encoded)
        assert ratio > 0

    q = exact_integer(candidate["weight_denominator"])
    vector_denom = exact_integer(base["vector_denominator"])
    t = q * vector_denom**2
    gamma_num = exact_integer(candidate["gamma_numerator_at_common_denominator"])
    assert q > 0 and vector_denom > 0 and t % 2 == 0 and gamma_num > 0
    gamma = Fraction(gamma_num, t)

    lines = iter((DATA / "basis.txt").read_text().splitlines())
    nvars, block_count = map(int, next(lines).split())
    assert nvars == base["variables"] and block_count == base["psd_blocks"]
    blocks, offset = [], 0
    for _ in range(block_count):
        order, _, dimension = map(int, next(lines).split())
        flags = [tuple(map(int, next(lines).split())) for _ in range(dimension)]
        blocks.append((order, dimension, offset, flags))
        offset += dimension**2
    assert next(lines, None) is None

    factors, weights = base["rank_one_factors"], candidate["factor_weights"]
    assert len(factors) == len(weights) == base["nonzero_rank_one_factors"]
    gram = [0] * offset
    additional = candidate.get("extra_rank_one_factors", [])
    all_factors = list(zip(factors, map(exact_integer, weights)))
    all_factors.extend((factor, exact_integer(factor["weight_numerator"])) for factor in additional)
    for factor, weight in all_factors:
        assert weight >= 0
        j = exact_integer(factor["block"])
        assert 0 <= j < block_count
        _, dimension, start, _ = blocks[j]
        vector = list(map(exact_integer, factor["vector_numerators"]))
        assert len(vector) == dimension
        if weight:
            for a, x in enumerate(vector):
                for b, y in enumerate(vector):
                    gram[start + a * dimension + b] += weight * x * y

    residual = [0] * nvars
    idx4 = read_array(DATA / "idx4.bin", "i")
    assert len(idx4) == 3**5
    for code, orbit in enumerate(idx4):
        if orbit >= 0 and colors(4, code)[-1] == 2:
            residual[orbit] -= t // 2
    q_cycle, target = cycle_expression(mode, nvars,ratio)
    target_scale = ratio.denominator if mode == "conditional" else 1
    assert gamma_num % target_scale == 0
    for j, coefficient in target.items():
        residual[j] -= (gamma_num // target_scale) * coefficient

    rows, _ = degree_row_names(DATA)
    degree_weights = list(map(exact_integer, candidate["degree_weights_numerators"]))
    assert len(rows) == base["equations"] == len(degree_weights)
    raw = sum(x for (k, _, _), x in zip(rows, degree_weights) if k == 2)
    dkeys, dvalues = read_sparse(DATA / "degree_keys.bin", DATA / "degree_values.bin",
                                 len(rows), nvars)
    for key, value in zip(dkeys, dvalues):
        i, j = divmod(key, nvars)
        residual[j] += degree_weights[i] * value

    for order, dimension, start, flags in blocks:
        if order == 2:
            units = [i for i, (n, _) in enumerate(flags) if n == 2]
            assert len(units) == 1
            u = units[0]
            raw += gram[start + u * dimension + u]
    gkeys, gvalues = read_sparse(DATA / "keys.bin", DATA / "values.bin", offset, nvars)
    for key, value in zip(gkeys, gvalues):
        i, j = divmod(key, nvars)
        residual[j] -= gram[i] * value

    excluded = red_triangle_coordinates() if triangle_free else set()
    assert not excluded or max(excluded) < nvars
    correction = sum(-r for j, r in enumerate(residual) if r < 0 and j not in excluded)
    cap = Fraction(raw + correction, t)
    cycle_cost = {"abundance": Fraction(1,8), "anchor": Fraction(0),
                  "conditional": ratio/8}[mode]
    reference = Fraction(5, 4) - gamma * cycle_cost
    epsilon = max(cap - reference, 0)
    assert epsilon <= max_error and gamma >= {
        "abundance": Fraction(3, 5), "anchor": Fraction(19, 100),
        "conditional": Fraction(0)
    }[mode]
    out = {
        "exact_integer_dual_verified": True,
        "mode": mode,
        "cycle_coordinate": q_cycle,
        "target_coefficients": target,
        "target_denominator": target_scale,
        "gamma": str(gamma),
        "epsilon": str(epsilon),
        "epsilon_decimal": float(epsilon),
        "cap": str(cap),
        "raw_cap": str(Fraction(raw, t)),
        "negative_coefficients": sum(r < 0 for r in residual),
        "correction": str(Fraction(correction, t)),
        "rank_one_weights_checked": len(all_factors),
        "additional_rank_one_weights_checked": len(additional),
        "degree_nonzeros_checked": len(dkeys),
        "gram_nonzeros_checked": len(gkeys),
        "candidate_sha256": sha256(candidate_path.read_bytes()).hexdigest(),
        "base_sha256": BASE_HASH,
        "matrix_sha256": {name: sha256((DATA / name).read_bytes()).hexdigest() for name in
                         ["basis.txt", "degree.txt", "idx4.bin", "idx5.bin", "keys.bin",
                          "values.bin", "degree_keys.bin", "degree_values.bin"]},
    }
    if mode in {"anchor", "conditional"}:
        out["order6_index_sha256"] = sha256((DATA / "order6_orbit_index.bin").read_bytes()).hexdigest()
    if mode == "conditional":
        out["anchor_ratio"] = str(ratio)
        out["verified_support_gap"] = str(Fraction(5,4)-cap)
    if triangle_free:
        out["red_triangle_coordinates_zero"] = len(excluded)
    return out


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run without -O/-OO or PYTHONOPTIMIZE.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("candidate", type=Path)
    args = parser.parse_args()
    print(json.dumps(verify(args.candidate), indent=2))

