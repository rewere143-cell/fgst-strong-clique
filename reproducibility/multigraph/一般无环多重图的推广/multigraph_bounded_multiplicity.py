"""Exact inclusion--exclusion rows when parallel multiplicity is bounded."""

from collections import defaultdict
from math import gcd

from multigraph_lift_probe import decode
from multigraph_weighted_ore_model import permutation_slots


def capped_tag_rows(data, multiplicity):
    import numpy as np
    from scipy.sparse import coo_matrix

    assert type(multiplicity) is int and 2 <= multiplicity <= 20
    limit = multiplicity-1
    groups = defaultdict(dict)
    for i, (n, code, mask) in enumerate(zip(data["order"], data["code"], data["mask"])):
        groups[int(n), int(code)][int(mask)] = i
    slots = {n: np.asarray(permutation_slots(n), dtype=np.int64)
             for n in range(2, int(max(data["order"]))+1)}
    rows, cols, vals = [], [], []
    count = 0

    def subsets(mask):
        use = mask
        while True:
            yield use
            if not use:
                return
            use = (use-1)&mask

    for (n, code), refs in groups.items():
        if len(refs) == 1:
            continue
        colors = np.asarray(decode(n, code))
        maps = slots[n][np.all(colors[slots[n]] == colors, axis=1)]
        bits = (1 << maps)
        remap = np.arange(len(colors), dtype=np.int64)
        nice = {}

        def canonical(mask):
            if mask not in nice:
                take = ((mask >> remap)&1) > 0
                best = int(np.min(np.sum(bits[:, take], axis=1)))
                nice[mask] = refs[best]
            return nice[mask]

        seen = set()
        for chosen in refs:
            if not chosen:
                continue
            for truth in subsets(chosen):
                if truth == chosen:
                    continue
                unset = chosen ^ truth
                vector = defaultdict(int)
                for added in subsets(unset):
                    i = canonical(added | truth)
                    sign = (-1)**added.bit_count()
                    coeff = (limit**(unset.bit_count()-added.bit_count()))*int(data["aut_count"][i])
                    vector[i] -= sign*coeff
                factor = gcd(*vector.values())
                row = tuple((i, x//factor) for i, x in sorted(vector.items()) if x)
                if row in seen:
                    continue
                seen.add(row)
                cols.extend(i for i, _ in row)
                vals.extend(x for _, x in row)
                rows.extend([count]*len(row))
                count += 1
    return coo_matrix((vals, (rows, cols)), shape=(count, len(data["order"])), dtype=np.int64).tocsr()
