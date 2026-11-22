"""Degree-nine weighted-flag searches using finite root degree relations."""

import argparse
from collections import defaultdict
from fractions import Fraction
from functools import cache
from itertools import combinations
import json
from math import gcd
from pathlib import Path
import sys


HERE = Path(__file__).resolve().parent
BASE = HERE.parent
sys.path[:0] = [str(BASE), str(BASE / "三小时续研_旗证书")]

from k5_turan_rows import contains_red_clique
from multigraph_lift_probe import decode, edge_pairs
from multigraph_weighted_maxdeg_exact import build_integer, verify
from multigraph_weighted_ore_model import permutation_slots


CACHE = BASE / "multigraph_weighted_maxdeg_5"
SEED = BASE / "multigraph_maxdeg5_mu2_certificate.json"
D = 9


def finite_root_rows(data):
    import numpy as np
    from scipy.sparse import csr_matrix, vstack

    by_order = {n: np.flatnonzero(data["order"] == n) for n in range(2, 6)}
    slots = {n: np.asarray(permutation_slots(n)) for n in by_order}
    edge_index = {n: {pair: i for i, pair in enumerate(edge_pairs(n))} for n in by_order}
    colors = {}
    prepared = {}
    for n, indices in by_order.items():
        grouped = defaultdict(list)
        for i in indices:
            grouped[int(data["code"][i])].append(int(i))
        for code, rows in grouped.items():
            colors[n, code] = np.asarray(decode(n, code))[slots[n]]
            prepared[n, code] = (
                rows, np.asarray([int(data["mask"][i]) for i in rows]),
            )

    @cache
    def extension(root_tag, functions):
        n = len(functions) + 2
        pairs = edge_index[n]
        permutations = slots[n]
        root = pairs[0, 1]
        mask = (1 << permutations[:, root]) * int(root_tag)
        filters = []
        for v, kind in enumerate(functions, 2):
            edge_x, edge_y = pairs[0, v], pairs[1, v]
            if kind == "c":
                filters.append((edge_x, 1))
                filters.append((edge_y, 1))
            else:
                edge = edge_x if kind.startswith("x") else edge_y
                filters.append((edge, 2))
                if kind.endswith("j"):
                    mask |= 1 << permutations[:, edge]
        out = np.zeros(len(data["order"]), dtype=np.int64)
        for (order, code), (rows, tags) in prepared.items():
            if order != n:
                continue
            color = colors[n, code]
            valid = color[:, root] == 2
            for e, level in filters:
                valid &= color[:, e] >= level
            if valid.any():
                out[rows] = np.count_nonzero(tags[:, None] == mask[valid], axis=1) * D**(n-2)
        return csr_matrix(out)

    def row(root_tag, terms):
        return sum(coefficient * extension(root_tag, tuple(sorted(monomial)))
                   for coefficient, monomial in terms)

    inequalities = []
    equalities = []
    for root_tag in (False, True):
        # xj is the number of extra marked copies incident to the first root.
        inequalities.append(row(root_tag, ((1, ("xj",)), (-2, ()))))
        inequalities.append(row(root_tag, ((-1, ("xj", "xj")), (1, ("xj",)))))
        inequalities.append(row(root_tag, ((-1, ("xj", "xj")), (3, ("xj",)), (-2, ()))))
    equalities.append(row(False, ((1, ("xj", "xj", "xj")), (-3, ("xj", "xj")), (2, ("xj",)))))
    # A doubled root has excess incident degrees 1 or 2, with at most one
    # endpoint attaining 2. Its post-padding distinct common degree is at most 1.
    inequalities.append(row(True, ((1, ("xj",)), (1, ("yj",)), (1, ("c",)), (-3, ()))))
    equalities.extend((
        row(True, ((1, ("xj", "yj")), (-1, ("xj",)), (-1, ("yj",)), (1, ()))),
        row(True, ((1, ("c", "c")), (-1, ("c",)))),
        row(True, ((1, ("c", "xj")), (1, ("c", "yj")), (-2, ("c",)))),
    ))
    for level in range(D):
        # h_s is the first-copy marked degree, and is integer.
        inequalities.append(row(False, ((-1, ("xh", "xh")), (2*level+1, ("xh",)),
                                        (-level*(level+1), ()))))
    return vstack(equalities, format="csr"), vstack(inequalities, format="csr")


def impossible_patterns(data, triangle_free):
    import numpy as np

    forbidden = np.zeros(len(data["order"]), dtype=np.int64)
    for i, (order, code, tags) in enumerate(zip(data["order"], data["code"], data["mask"])):
        if order < 3:
            continue
        pairs = edge_pairs(int(order))
        color = decode(int(order), int(code))
        for a, b, c in combinations(range(order), 3):
            edges = [pairs.index(pair) for pair in ((a, b), (a, c), (b, c))]
            if all(color[e] == 2 for e in edges) and (triangle_free or any(tags >> e & 1 for e in edges)):
                forbidden[i] = 1
                break
    return forbidden


def system(settings):
    import numpy as np
    from scipy.sparse import csr_matrix, vstack

    eq, iq, grams, sizes, data, tags, scale, objective, roots = build_integer(CACHE, settings)
    extra_eq, extra_iq = finite_root_rows(data)
    forbidden = impossible_patterns(data, settings["d9_triangle_free"])
    forbidden |= contains_red_clique(data, 4)
    target = Fraction(97, 81)
    marked_mass = Fraction(98, 81)
    mult = (2 * target.denominator) // gcd(scale, 2 * target.denominator)
    new_scale = scale * mult
    root = csr_matrix(np.where((data["order"] == 2) & (tags == 0), 2, 0))
    norm = csr_matrix(data["normalizer"].astype(np.int64))
    projected = csr_matrix(np.where(tags == 0, objective, 0))
    mixed = csr_matrix(np.where(tags == 1, objective, 0))
    support_bound = (new_scale//2) * projected - int(new_scale * target) * root
    total_mass = (new_scale//2) * csr_matrix(objective) - int(new_scale * marked_mass) * norm
    support_mass = (new_scale//2) * projected + (new_scale//4) * mixed - int(new_scale * marked_mass) * root
    result = (vstack((eq*mult, extra_eq*new_scale, total_mass, support_mass), format="csr"),
              vstack((iq*mult, extra_iq*new_scale, csr_matrix(forbidden)*new_scale,
                      support_bound), format="csr"),
              [g*mult for g in grams], sizes, data, tags, new_scale, objective, roots)
    print(json.dumps({"equations": result[0].shape[0], "inequalities": result[1].shape[0],
                      "zero_coordinates": int(forbidden.sum()), "scale": new_scale}), flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("--vendor", type=Path)
    parser.add_argument("--seconds", type=int, default=1500)
    parser.add_argument("--rounds", type=int, default=20)
    parser.add_argument("--replay", action="store_true")
    parser.add_argument("--triangle-free", action="store_true")
    parser.add_argument("--b-low", type=int, default=1)
    parser.add_argument("--b-high", type=int, default=18)
    args = parser.parse_args()
    if not __debug__:
        raise RuntimeError("Run with Python assertions enabled")
    if args.vendor:
        sys.path.insert(0, str(args.vendor))
    if args.replay:
        cert = json.loads(args.certificate.read_bytes())
        assert cert["settings"]["mass_low"] == cert["settings"]["mass_high"] == "98/81"
        print(json.dumps(verify(CACHE, cert, system(cert["settings"])), indent=2))
        return
    from rank_cut_search import search

    cert = json.loads(SEED.read_bytes())
    cert["settings"].update(mass_low="98/81", mass_high="98/81", local_beta="2973/10000",
                            e_low=str(Fraction(args.b_low, 98)), e_high=str(Fraction(args.b_high, 98)),
                            d9_triangle_free=args.triangle_free)
    data = system(cert["settings"])
    search(cert, data, args.certificate, args.seconds, args.rounds, 1100, 0, 100,
           False, None, False, None, 1, None)


if __name__ == "__main__":
    main()
