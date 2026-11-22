#!/usr/bin/env python3
"""Exact rank-one dual verification against exhaustively audited sparse data.

All algebra uses Python integers and fractions. No optimizer, floating-point
eigenvalue test, production builder, or nonstandard Python package is used.
"""
from array import array
from fractions import Fraction
from pathlib import Path
import argparse
import hashlib
import json
import sys

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "data"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def exact_int(value):
    if type(value) is int:
        return value
    if type(value) is str and value and value.lstrip("-").isdigit():
        # int rejects multiple signs; no float-to-int conversion is permitted.
        return int(value)
    raise ValueError("Expected an integer or a decimal integer string")


def read_array(name, kind):
    value = array(kind)
    raw = (DATA / name).read_bytes()
    require(len(raw) % value.itemsize == 0, "Partial binary integer")
    value.frombytes(raw)
    if sys.byteorder != "little":
        value.byteswap()
    return value


def colors(n, code):
    result = [2]
    for _ in range(n * (n - 1) // 2 - 1):
        result.append(code % 3)
        code //= 3
    require(code == 0, "Pattern code out of range")
    return tuple(result)


def verify(certificate):
    # Duplicate JSON keys would obscure the artifact and are explicitly rejected.
    def object_pairs(pairs):
        out = {}
        for key, value in pairs:
            require(key not in out, "Duplicate JSON key")
            out[key] = value
        return out

    obj = json.loads(certificate.read_text(encoding="utf-8"), object_pairs_hook=object_pairs)
    denominator = exact_int(obj["common_denominator"])
    weight_denominator = exact_int(obj["weight_denominator"])
    vector_denominator = exact_int(obj["vector_denominator"])
    require(weight_denominator > 0 and vector_denominator > 0, "Positive denominators required")
    require(denominator == weight_denominator * vector_denominator ** 2, "Denominator relation")
    require(denominator % 2 == 0, "Even objective denominator required")
    lines = iter((DATA / "basis.txt").read_text().splitlines())
    variables, count = map(int, next(lines).split())
    require((variables, count) == (23789, 57), "Unexpected model dimensions")
    blocks = []
    offset = 0
    for _ in range(count):
        k, pattern, size = map(int, next(lines).split())
        flags = [tuple(map(int, next(lines).split())) for _ in range(size)]
        blocks.append((k, pattern, size, offset, flags))
        offset += size * size
    require(list(lines) == [], "Trailing basis data")
    require(exact_int(obj["variables"]) == variables and exact_int(obj["psd_blocks"]) == count, "Certificate dimensions")
    gram = [0] * offset
    factors = obj["rank_one_factors"]
    positive_factors = 0
    for factor in factors:
        block = exact_int(factor["block"])
        weight = exact_int(factor["weight_numerator"])
        require(0 <= block < count, "Block out of range")
        require(weight >= 0, "Negative rank-one weight")
        positive_factors += weight > 0
        k, pattern, size, begin, flags = blocks[block]
        vector = [exact_int(x) for x in factor["vector_numerators"]]
        require(len(vector) == size, "Vector dimension")
        for i, x in enumerate(vector):
            for j, y in enumerate(vector):
                gram[begin + i * size + j] += weight * x * y
    require(exact_int(obj["nonzero_rank_one_factors"]) == positive_factors, "Factor count")
    residual = [0] * variables
    index4 = read_array("idx4.bin", "i")
    require(len(index4) == 243, "Order-four index length")
    # The 23-pair is the last base-three digit of an order-four code.
    for code, coordinate in enumerate(index4):
        if coordinate >= 0 and code // 81 % 3 == 2:
            require(coordinate < variables, "Objective coordinate")
            residual[coordinate] -= denominator // 2
    rows = (DATA / "degree.txt").read_text().splitlines()
    row_count = int(rows[0])
    require(row_count == 3516 == exact_int(obj["equations"]), "Degree row count")
    weights, names = [], []
    raw = 0
    for line in rows[1:]:
        k, code, vertex = map(int, line.split())
        name = f"degree_{k}_{colors(k, code)}_{vertex}"
        weight = exact_int(obj["degree_weights_numerators"].get(name, 0))
        names.append(name)
        weights.append(weight)
        if k == 2:
            raw += weight
    require(len(weights) == row_count and len(set(names)) == row_count, "Duplicate or missing rows")
    require(set(obj["degree_weights_numerators"]) <= set(names), "Unknown degree multiplier")
    dkeys, dvalues = read_array("degree_keys.bin", "q"), read_array("degree_values.bin", "i")
    require(len(dkeys) == len(dvalues) == 433899, "Degree sparse length")
    require(all(0 <= key < row_count * variables for key in dkeys), "Degree key range")
    require(all(x < y for x, y in zip(dkeys, dkeys[1:])), "Duplicate or unsorted degree key")
    for key, value in zip(dkeys, dvalues):
        row, coordinate = divmod(key, variables)
        residual[coordinate] += weights[row] * value
    for k, pattern, size, begin, flags in blocks:
        if k == 2:
            units = [i for i, (n, code) in enumerate(flags) if n == 2]
            require(len(units) == 1, "Root-type constant")
            unit = units[0]
            raw += gram[begin + unit * size + unit]
    keys, values = read_array("keys.bin", "q"), read_array("values.bin", "i")
    require(len(keys) == len(values) == 1895405, "Gram sparse length")
    require(all(0 <= key < offset * variables for key in keys), "Gram key range")
    require(all(x < y for x, y in zip(keys, keys[1:])), "Duplicate or unsorted Gram key")
    for key, value in zip(keys, values):
        row, coordinate = divmod(key, variables)
        residual[coordinate] -= gram[row] * value
    # This archival release proves the sharp bound without a correction budget.
    require(all(value >= 0 for value in residual), "Negative scalar residual")
    require(obj["negative_residual_numerators"] == {}, "Nonempty correction map")
    require(exact_int(obj["negative_residual_count"]) == 0, "Nonzero negative count")
    require(Fraction(obj["rounding_correction"]) == 0, "Nonzero rounding correction")
    require(Fraction(raw, denominator) == Fraction(5, 4), "Raw dual bound differs from 5/4")
    require(Fraction(obj["rational_bound"]) == Fraction(5, 4), "Claimed bound differs from 5/4")
    require(Fraction(obj["raw_dual_value"]) == Fraction(5, 4), "Claimed raw value differs from 5/4")
    result = {
        "all_passed": True,
        "certificate_sha256": hashlib.sha256(certificate.read_bytes()).hexdigest(),
        "variables": variables, "degree_rows": row_count, "psd_blocks": count,
        "positive_rank_one_factors": positive_factors,
        "common_denominator": str(denominator),
        "weight_denominator": str(weight_denominator),
        "vector_denominator": str(vector_denominator),
        "raw_dual_numerator": str(raw), "exact_bound": "5/4", "rounding_correction": "0",
        "degree_nonzeros_checked": len(dkeys), "gram_nonzeros_checked": len(keys),
        "residual_count": len(residual),
        "positive_residuals": sum(x > 0 for x in residual),
        "zero_residuals": sum(x == 0 for x in residual),
        "negative_residuals": sum(x < 0 for x in residual),
        "maximum_residual_numerator": str(max(residual)),
        "order_three_defect_residual_numerators": {str(i): str(residual[i]) for i in (0, 2, 3, 4)},
        "arithmetic": "Python arbitrary precision integers and fractions; no floating-point algebra",
    }
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certificate", type=Path, default=DATA / "compact_certificate.json")
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    result = verify(args.certificate)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))
