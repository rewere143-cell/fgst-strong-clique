"""Evaluate the new red-clique constraints on finite weighted hosts."""
import argparse
from fractions import Fraction as F
import json
from pathlib import Path
import sys


HERE = Path(__file__).resolve().parent
BASE = HERE.parent
sys.path.insert(0, str(BASE))

from audit_multigraph_type_forest_psd import direct_maps, tag_weight
from k5_turan_rows import (clique_repeat_rows, common_neighbor_rows, contains_red_k5,
                           triangle_signature_rows)


def evaluate(data, colors, weights):
    import numpy as np

    n = len(colors)
    degree = [sum(int(c != 0) + w for c, w in zip(row, tagged))
              for row, tagged in zip(colors, weights)]
    D = max(degree)
    m = sum(1 + weights[i][j] for i in range(n) for j in range(i) if colors[i][j] == 2)
    order = int(max(data["order"]))
    maps = {k: direct_maps(colors, k) for k in range(2, order + 1)}
    scaled = np.zeros(len(data["order"]), dtype=np.int64)
    for row, (k, color, mask, aut) in enumerate(zip(data["order"], data["code"],
                                                   data["mask"], data["aut_count"])):
        maps_for_type = maps[int(k)].get(int(color), ())
        total = sum(tag_weight(weights, phi, int(mask)) for phi in maps_for_type)
        scaled[row] = total * D**(order - int(k)) * (720 // int(aut))
    assert int(contains_red_k5(data) @ scaled) == 0
    turan = common_neighbor_rows(data) @ scaled
    assert max(turan) <= 0
    clique = [sum(coefficient * int((row @ scaled)[0]) for coefficient, row in inequality)
              for inequality in clique_repeat_rows(data, F(m, D*D), include_losses=True)]
    assert max(clique) <= 0
    triangle = [sum(coefficient * int((row @ scaled)[0]) for coefficient, row in inequality)
                for inequality in triangle_signature_rows(data, F(m, D*D), stronger=True)]
    assert max(triangle) <= 0
    return {"vertices": n, "D": D, "m": m, "turan_rows": len(turan), "clique_rows": len(clique),
            "triangle_rows": len(triangle)}


def run():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--vendor", type=Path)
    args = parser.parse_args()
    if args.vendor:
        sys.path.insert(0, str(args.vendor))
    import numpy as np

    data = dict(np.load(BASE / "multigraph_weighted_maxdeg_5.data.npz"))
    partition = [0, 1, 2, 3, 1, 2]
    multipartite = [[2 * int(j != i and partition[i] != partition[j])
                     for j in range(6)] for i in range(6)]
    complete_host = [[0 if i == j else 2 if max(i, j) < 4 or (i + j) % 3 == 0 else 1
                      for j in range(6)] for i in range(6)]
    cycle = [[2 * int((j-i) % 5 in (1, 4)) for j in range(5)] for i in range(5)]
    reports = []
    for colors in (multipartite, complete_host, cycle):
        extras = [[(i*j+i+j) % 3 if c == 2 else 0 for j, c in enumerate(row)]
                  for i, row in enumerate(colors)]
        reports.append(evaluate(data, colors, extras))
    print(json.dumps({"verified": True, "cases": reports}, indent=2))


if __name__ == "__main__":
    run()
