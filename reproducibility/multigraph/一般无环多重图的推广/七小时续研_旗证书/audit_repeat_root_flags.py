"""Audit the ordered doubled-root spoke rows on finite host graphs."""
import argparse
from pathlib import Path
import sys

from odd_shadow_model import CACHE
from audit_multigraph_type_forest_psd import direct_maps, tag_weight
from d9_repeat_root_rows import repeated_root_neighborhood_rows


def host(overlap, blue):
    left = tuple(range(2, 9))
    right = ((8,) if overlap else ()) + tuple(range(9, 16-overlap))
    n = 16-overlap
    colors = [[0]*n for _ in range(n)]
    extra = [[0]*n for _ in range(n)]
    colors[0][1] = colors[1][0] = 2
    extra[0][1] = extra[1][0] = 1
    for i, (root, leaf) in enumerate((u,v) for u,group in enumerate((left,right)) for v in group):
        colors[root][leaf] = colors[leaf][root] = 1 if i < blue else 2
    return colors, extra


def audit(vendor):
    if vendor:
        sys.path.insert(0, str(vendor))
    import numpy as np

    data = dict(np.load(CACHE.with_suffix(".data.npz")))
    counts = repeated_root_neighborhood_rows(data)
    for overlap, blue in ((0, 1), (1, 1), (0, 9)):
        colors, extra = host(overlap, blue)
        maps = {n: direct_maps(colors, n) for n in range(2, 6)}
        x = np.zeros(len(data["order"]), dtype=np.int64)
        for row, (n, code, mask, auto) in enumerate(
                zip(data["order"], data["code"], data["mask"], data["aut_count"])):
            if mask:
                assert 720 % int(auto) == 0
                count = sum(tag_weight(extra, placement, int(mask)) for placement in maps[n].get(code, ()))
                x[row] = count * 9**(5-int(n)) * (720//int(auto))
        values = (counts@x).reshape(-1,4)
        assert np.all(values <= 0)
        assert np.any(values < 0)
        assert np.all(values[:, 1 if blue == 9 else 0] == 0)
        assert np.all(values[:, 2 if overlap else 3] == 0)
        print(f"q_external={14-overlap}, blue={blue}, checked {values.size} rows")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--vendor", type=Path)
    audit(parser.parse_args().vendor)
