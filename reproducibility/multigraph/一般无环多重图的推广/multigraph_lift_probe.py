"""Exact diagnostic for the naive multiplicity lift of a simple flag certificate.

All computed inequalities concern individual colored flag coordinates. A
negative coordinate refutes this choice of multipliers, not the theorem.
"""

from array import array
from collections import defaultdict
from fractions import Fraction
from itertools import combinations, permutations, product
from pathlib import Path
import argparse
import hashlib
import json
import sys


def read_ints(path, kind):
    result = array(kind)
    with path.open("rb") as stream:
        result.fromfile(stream, path.stat().st_size // result.itemsize)
    if sys.byteorder != "little":
        result.byteswap()
    return result


def decode(n, code):
    colors = [2]
    for _ in range(n * (n - 1) // 2 - 1):
        colors.append(code % 3)
        code //= 3
    assert code == 0
    return tuple(colors)


def edge_pairs(n):
    return tuple(combinations(range(n), 2))


def encode(colors):
    return sum(value * 3**index for index, value in enumerate(colors[1:]))


def find_simple_residuals(cert, data, ids):
    T = int(cert["common_denominator"])
    Q = int(cert["weight_denominator"])
    R = int(cert["vector_denominator"])
    assert T == Q * R * R and Q > 0 and R > 0 and T % 2 == 0

    lines = iter((data / "basis.txt").read_text().splitlines())
    num_variables, num_blocks = map(int, next(lines).split())
    blocks = []
    offset = 0
    for _ in range(num_blocks):
        k, _, m = map(int, next(lines).split())
        basis = [tuple(map(int, next(lines).split())) for _ in range(m)]
        blocks.append((k, m, offset, basis))
        offset += m * m

    gram = [0] * offset
    for factor in cert["rank_one_factors"]:
        j = int(factor["block"])
        weight = int(factor["weight_numerator"])
        vector = list(map(int, factor["vector_numerators"]))
        assert 0 <= j < num_blocks and weight >= 0
        _, m, start, _ = blocks[j]
        assert m == len(vector)
        for a, x in enumerate(vector):
            if not x:
                continue
            for b, y in enumerate(vector):
                gram[start + a * m + b] += weight * x * y

    residual = [0] * num_variables
    for code, orbit in enumerate(ids[4]):
        if orbit >= 0 and decode(4, code)[-1] == 2:
            residual[orbit] -= T // 2

    degree_rows = (data / "degree.txt").read_text().splitlines()
    expected_rows = int(degree_rows[0])
    row_weights = []
    row_lookup = defaultdict(list)
    raw_constant = 0
    seen_names = set()
    for line in degree_rows[1:]:
        k, code, u = map(int, line.split())
        name = f"degree_{k}_{decode(k, code)}_{u}"
        seen_names.add(name)
        weight = int(cert["degree_weights_numerators"].get(name, 0))
        row_weights.append(weight)
        if weight:
            row_lookup[k, code].append((u, weight))
        if k == 2:
            raw_constant += weight
    assert expected_rows == len(row_weights)
    assert set(cert["degree_weights_numerators"]) <= seen_names

    degree_keys = read_ints(data / "degree_keys.bin", "q")
    degree_values = read_ints(data / "degree_values.bin", "i")
    assert len(degree_keys) == len(degree_values)
    for key, value in zip(degree_keys, degree_values):
        row, col = divmod(key, num_variables)
        residual[col] += row_weights[row] * value

    gram_constant = 0
    for k, m, start, basis in blocks:
        if k == 2:
            u, = [i for i, (n, _) in enumerate(basis) if n == 2]
            gram_constant += gram[start + u * m + u]
    raw_constant += gram_constant
    gram_keys = read_ints(data / "keys.bin", "q")
    gram_values = read_ints(data / "values.bin", "i")
    assert len(gram_keys) == len(gram_values)
    gram_coefficients = [0] * num_variables
    for key, value in zip(gram_keys, gram_values):
        row, col = divmod(key, num_variables)
        gram_coefficients[col] += gram[row] * value
    residual = [value - coefficient for value, coefficient in zip(residual, gram_coefficients)]

    assert Fraction(raw_constant, T) == Fraction(5, 4)
    assert all(value >= 0 for value in residual)
    return T, residual, row_lookup, gram_constant, gram_coefficients


def probe_refinements(n, code, idx, scale, simple_residual, row_lookup):
    """Check all double-mark choices on one simple representative.

    Divide a refined coefficient by the refinement multiplicity g = |Aut(F)|
    / |Aut(F*)|. After also multiplying by |Aut(F)|, the simple residual is
    |Aut(F)| * r_F. Degree-weight changes are computed over all permutations
    of the support pattern. Each attachment to a doubled mark adds its row
    multiplier. In order four, the objective gets the product of the two
    root multiplicities, summed over every ordering.
    """
    pairs = edge_pairs(n)
    colors = decode(n, code)
    marked = [pair for pair, color in zip(pairs, colors) if color == 2]
    pair_ids = {pair: index for index, pair in enumerate(marked)}
    mat = [[0] * n for _ in range(n)]
    for (u, v), color in zip(pairs, colors):
        mat[u][v] = mat[v][u] = color

    aut = 0
    changes = [0] * len(marked)
    disjoint_root_orders = defaultdict(int)
    prefix_pairs = edge_pairs(n - 1)
    for labels in permutations(range(n)):
        if mat[labels[0]][labels[1]] != 2:
            continue
        permuted = tuple(mat[labels[i]][labels[j]] for i, j in pairs)
        if permuted == colors:
            aut += 1

        extension_iv = labels[-1]
        prefix_code = encode(tuple(mat[labels[i]][labels[j]] for i, j in prefix_pairs))
        for u, weight in row_lookup[n - 1, prefix_code]:
            if mat[labels[u]][extension_iv] == 2:
                pair = tuple(sorted((labels[u], extension_iv)))
                changes[pair_ids[pair]] += weight

        if n == 4 and mat[labels[2]][labels[3]] == 2:
            first = pair_ids[tuple(sorted(labels[:2]))]
            second = pair_ids[tuple(sorted(labels[2:]))]
            disjoint_root_orders[first, second] += 1

    baseline = aut * simple_residual[idx]
    if n != 4:
        doubling = tuple(int(change < 0) for change in changes)
        minimum = baseline + sum(change * bit for change, bit in zip(changes, doubling))
    else:
        minimum = baseline
        doubling = tuple(0 for _ in marked)
        for bits in product((0, 1), repeat=len(marked)):
            objective_change = scale // 2 * sum(
                count * ((1 + bits[first]) * (1 + bits[second]) - 1)
                for (first, second), count in disjoint_root_orders.items()
            )
            value = baseline + sum(c * b for c, b in zip(changes, bits)) - objective_change
            if value < minimum:
                minimum = value
                doubling = bits
    if minimum >= 0:
        return None
    return {
        "order": n,
        "support_code": code,
        "support_coordinate": idx,
        "support_colors": colors,
        "double_these_pairs": [pair for pair, bit in zip(marked, doubling) if bit],
        "old_residual": str(Fraction(simple_residual[idx], scale)),
        "refined_residual_divided_by_g": str(Fraction(minimum, scale * aut)),
    }


def c5_orbits(ids):
    observed = {}
    for n in range(3, 7):
        for suffix in product(range(5), repeat=n - 2):
            images = (0, 1) + suffix
            colors = tuple(
                2 if (images[i] - images[j]) % 5 in (1, 4) else 0
                for i, j in edge_pairs(n)
            )
            code = encode(colors)
            idx = ids[n][code]
            if idx >= 0:
                observed[n, idx] = code
    assert len(observed) == 19
    return observed


def double_c5_fixed_q_test(ids, scale, gram_constant, gram_coefficients, c5):
    """Test reusing *any* degree multipliers with the old projected Q tensors.

    The double pentagon has m=10, weighted Delta=4 and simple support C5.
    Each oriented root edge has the same number of maps for a given support
    pattern. The marked-set normalization is twice the support-root count.
    """
    result = Fraction(gram_constant, 2 * scale)
    for (n, idx), code in c5.items():
        colors = decode(n, code)
        count = 0
        for suffix in product(range(5), repeat=n - 2):
            images = (0, 1) + suffix
            actual = tuple(
                2 if (images[i] - images[j]) % 5 in (1, 4) else 0
                for i, j in edge_pairs(n)
            )
            count += actual == colors
        assert count > 0
        result += Fraction(gram_coefficients[idx] * count, scale * 2 * 4 ** (n - 2))
    objective = Fraction(5, 8)
    return {
        "support": "C5 with both copies of every edge marked",
        "objective": str(objective),
        "projected_gram_contraction": str(result),
        "projected_gram_contraction_decimal": float(result),
        "objective_plus_gram_contraction": str(objective + result),
        "objective_plus_gram_exceeds_5_over_4": objective + result > Fraction(5, 4),
    }


def run(base, cert_path, exhaustive):
    data = base / "audit" / "flag_coefficients"
    ids = {n: read_ints(data / f"idx{n}.bin", "i") for n in range(3, 6)}
    ids[6] = read_ints(base / "flags" / "order6_orbit_index.bin", "i")
    ids[6] = array("i", (value + 728 if value >= 0 else value for value in ids[6]))
    cert = json.loads(cert_path.read_text())
    scale, residual, row_lookup, gram_constant, gram_coefficients = find_simple_residuals(cert, data, ids)
    c5 = c5_orbits(ids)

    if exhaustive:
        selected = {}
        for n in range(3, 7):
            for code, idx in enumerate(ids[n]):
                if idx >= 0:
                    selected.setdefault((n, idx), code)
    else:
        selected = c5

    issues = []
    counts = defaultdict(int)
    c5_issues = []
    for (n, idx), code in sorted(selected.items()):
        result = probe_refinements(n, code, idx, scale, residual, row_lookup)
        if result is not None:
            counts[n] += 1
            if (n, idx) in c5:
                c5_issues.append(result)
            if len(issues) < 20:
                issues.append(result)
    return {
        "naive_lift_valid": not issues,
        "simple_certificate_sha256": hashlib.sha256(cert_path.read_bytes()).hexdigest(),
        "simple_orbits_checked": len(selected),
        "negative_refinement_orbits_by_order": dict(counts),
        "c5_supported_orbits": len(c5),
        "fixed_projected_q_test": double_c5_fixed_q_test(
            ids, scale, gram_constant, gram_coefficients, c5
        ),
        "c5_supported_negative_refinements": c5_issues,
        "initial_negative_examples": issues,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("snapshot", type=Path)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("--exhaustive", action="store_true")
    args = parser.parse_args()
    print(json.dumps(run(args.snapshot, args.certificate, args.exhaustive), indent=2))


if __name__ == "__main__":
    main()
