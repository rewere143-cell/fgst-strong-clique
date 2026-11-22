"""Degree-five rows for red K5 exclusion and red common neighborhoods."""
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations

from multigraph_lift_probe import decode, edge_pairs, encode
from multigraph_weighted_ore_model import permutation_slots


def contains_red_clique(data, k):
    import numpy as np

    result = np.zeros(len(data["order"]), dtype=np.int64)
    for n in range(k, int(max(data["order"])) + 1):
        pairs = tuple(edge_pairs(n))
        subsets = tuple(
            tuple(pairs.index(pair) for pair in combinations(vertices, 2))
            for vertices in combinations(range(n), k)
        )
        found = {}
        for row in np.flatnonzero(data["order"] == n):
            code = int(data["code"][row])
            if code not in found:
                colors = decode(n, code)
                found[code] = any(all(colors[i] == 2 for i in subset) for subset in subsets)
            result[row] = found[code]
    return result


def contains_red_k5(data):
    return contains_red_clique(data, 5)


def forest_extendable_blue(data):
    """Indicate flags with a blue pair that extends the tag forest."""
    import numpy as np

    selected = np.zeros(len(data["order"]), dtype=bool)
    for n in range(3, int(max(data["order"]))+1):
        pairs = tuple(edge_pairs(n))
        blue_pairs = {}
        for row in np.flatnonzero(data["order"] == n):
            code = int(data["code"][row])
            if code not in blue_pairs:
                blue_pairs[code] = tuple(pair for pair, color in zip(pairs, decode(n, code))
                                         if color == 1)
            blue = blue_pairs[code]
            if not blue:
                continue
            forest = int(data["mask"][row])
            components = list(range(n))

            def find(x):
                while components[x] != x:
                    x = components[x]
                return x

            for i, (u, v) in enumerate(pairs):
                if forest & (1 << i):
                    components[find(u)] = find(v)
            selected[row] = any(find(u) != find(v) for u, v in blue)
    return selected


def connected(n, colors):
    seen = {0}
    while True:
        expanded = seen.copy()
        for (i, j), color in zip(edge_pairs(n), colors):
            if color and (i in seen or j in seen):
                expanded.update((i, j))
        if len(expanded) == n:
            return True
        if expanded == seen:
            return False
        seen = expanded


def common_neighbor_rows(data):
    """Condition the red Turan estimate on a labeled base and its tag weight."""
    import numpy as np
    from scipy.sparse import coo_matrix

    # Use exact integer coefficients in sparse rows. The extension positions
    # enumerate ordered common marked-neighbor pairs with replacement.
    terms = defaultdict(lambda: defaultdict(lambda: defaultdict(int)))
    for n in (4, 5):
        k = n - 2
        pairs = tuple(edge_pairs(n))
        slots = {pair: i for i, pair in enumerate(pairs)}
        small_pairs = tuple(edge_pairs(k))
        base_slots = tuple(slots[pair] for pair in small_pairs)
        bit_sets = []
        for perm in permutation_slots(n):
            allowed = tuple(1 << perm[i] for i in base_slots)
            ext = (1 << perm[slots[(0, k)]], 1 << perm[slots[(0, k + 1)]])
            bit_sets.append((perm, allowed, sum(allowed), ext, sum(ext)))
        # Same coloring may support multiple forest decorations.
        classifications = {}
        for row in np.flatnonzero(data["order"] == n):
            code, decoration = int(data["code"][row]), int(data["mask"][row])
            if code not in classifications:
                colors = decode(n, code)
                selected = []
                for perm, allowed, base_bits, ext, ext_bits in bit_sets:
                    base_colors = tuple(colors[perm[i]] for i in base_slots)
                    if 2 not in base_colors or not connected(k, base_colors):
                        continue
                    # The implicit first pair is omitted from this key. If
                    # several actual types contribute, their individually
                    # valid inequalities are added with equal weights.
                    base_code = encode(base_colors)
                    is_red = colors[perm[slots[(k, k + 1)]]] == 2
                    for a in (1, 2):
                        if a == 2 and colors[perm[slots[(0, 1)]]] != 2:
                            continue
                        if all(colors[perm[slots[(i, j)]]] == 2
                               for i in range(a) for j in range(k, n)):
                            difference = (4 - a)*is_red - (3 - a)
                            selected.append((a, base_code, allowed, base_bits, ext_bits, difference))
                classifications[code] = selected
            for a, base_code, allowed, base_bits, ext_bits, difference in classifications[code]:
                if decoration & ~(base_bits | ext_bits):
                    continue
                base_mask = sum((1 << j) for j, bit in enumerate(allowed) if decoration & bit)
                depth = (ext_bits & decoration).bit_count()
                terms[k, a, base_code, base_mask][depth][int(row)] += difference

    ii, jj, cc = [], [], []
    row_count = 0
    for key, powers in sorted(terms.items()):
        variants = ((1, 0, 0),)
        if key[-1].bit_count() <= 1:
            # w_x = 1 + t b_{0x} at t=1 and t=2, and w_x = b_{0x}.
            variants += ((1, 1, 1), (1, 2, 4), (0, 0, 1))
        for coefficients in variants:
            this_row = defaultdict(int)
            for power, coeff in enumerate(coefficients):
                if coeff:
                    for col, value in powers.get(power, {}).items():
                        this_row[col] += coeff * value
            if not any(this_row.values()):
                continue
            for col, value in this_row.items():
                if value:
                    ii.append(row_count)
                    jj.append(col)
                    cc.append(value)
            row_count += 1
    return coo_matrix((cc, (ii, jj)), shape=(row_count, len(data["order"])),
                      dtype=np.int64).tocsr()


def clique_repeat_rows(data, mass_lower, include_losses=False):
    """Decorated K_k rows for J_A / D <= k - (k-1) M_lower."""
    import numpy as np
    from scipy.sparse import csr_matrix

    parents, extensions = defaultdict(list), defaultdict(lambda: defaultdict(int))
    for n in range(2, 6):
        pairs = tuple(edge_pairs(n))
        for row in np.flatnonzero(data["order"] == n):
            colors = decode(n, int(data["code"][row]))
            tags = int(data["mask"][row])
            if n <= 4 and all(c == 2 for c in colors) and tags.bit_count() <= 2:
                degrees = [0] * n
                for j, (x, y) in enumerate(pairs):
                    if tags & (1 << j):
                        degrees[x] += 1
                        degrees[y] += 1
                parents[n, tuple(sorted(degrees))].append(int(row))
            if n == 2 or n > 5 or not tags:
                continue
            for x in range(n):
                internal = [(j, u, v) for j, (u, v) in enumerate(pairs) if x != u and x != v]
                if any(colors[j] != 2 for j, _, _ in internal):
                    continue
                base_tags = sum(bool(tags & (1 << j)) for j, _, _ in internal)
                if base_tags + 1 != tags.bit_count():
                    continue
                degrees = [0] * n
                for j, u, v in internal:
                    if tags & (1 << j):
                        degrees[u] += 1
                        degrees[v] += 1
                del degrees[x]
                extensions[n - 1, tuple(sorted(degrees))][int(row)] += 1
    assert extensions.keys() <= parents.keys()
    size = len(data["order"])
    losses = clique_loss_coefficients(data) if include_losses else {}

    def sparse_row(items):
        return csr_matrix(([value for _, value in items], ([0]*len(items), [key for key, _ in items])),
                          shape=(1, size), dtype=np.int64)

    rows = []
    for key, parent_indices in sorted(parents.items()):
        n, _ = key
        ext = sparse_row(tuple(extensions[key].items()))
        parent = sparse_row(tuple((i, 1) for i in parent_indices))
        cap = F(n) - (n - 1)*F(mass_lower)
        rows.append(((F(1), ext), (-cap, parent)))
        if n <= 3 and include_losses:
            loss = sparse_row(tuple(losses.get(key, {}).items()))
            rows.append(((F(1), ext + loss), (-cap, parent)))
    return rows


def clique_loss_coefficients(data):
    """Blue degree and common-anchor overlap terms for K2 and K3 bases."""
    import numpy as np

    extensions = defaultdict(lambda: defaultdict(int))
    for n in (4, 5):
        pairs = tuple(edge_pairs(n))
        slots = {pair: j for j, pair in enumerate(pairs)}
        splits = []
        for v, w in combinations(range(n), 2):
            root = tuple(x for x in range(n) if x not in (v, w))
            interior = tuple((slots[u, x], i, j) for i, u in enumerate(root)
                             for j, x in enumerate(root) if i < j)
            flags = tuple((slots[min(u, v), max(u, v)], slots[min(u, w), max(u, w)])
                          for u in root)
            slot = slots[v, w]
            splits.append((interior, flags, slot, sum(1 << j for j, _, _ in interior)))
        for row in np.flatnonzero(data["order"] == n):
            tags = int(data["mask"][row])
            colors = decode(n, int(data["code"][row]))
            for interior, flags, slot, base in splits:
                edge = colors[slot]
                if (not edge or tags & ~(base | (1 << slot))
                    or any(colors[j] != 2 for j, _, _ in interior)):
                    continue
                if edge == 1:
                    # Either orientation can designate the middle vertex.
                    value = sum(bool(colors[j]) + bool(colors[k]) for j, k in flags)
                else:
                    # Red pairs are unordered, with optional extra tag.
                    value = sum(bool(colors[j] and colors[k]) for j, k in flags)
                if not value:
                    continue
                degrees = [0]*(n - 2)
                for j, i, k in interior:
                    if tags & (1 << j):
                        degrees[i] += 1
                        degrees[k] += 1
                key = n - 2, tuple(sorted(degrees))
                extensions[key][int(row)] += value
    return extensions


def triangle_signature_rows(data, mass_lower, stronger=False):
    """Degree-five Ore constraints around a marked triangle."""
    import numpy as np
    from scipy.sparse import csr_matrix

    beta = F(1489, 5000)
    masses = defaultdict(lambda: defaultdict(lambda: defaultdict(int)))
    for n in (3, 4, 5):
        entries = tuple(edge_pairs(n))
        slots = {edge: i for i, edge in enumerate(entries)}

        def slot(u, v):
            return slots[min(u, v), max(u, v)]

        parts = []
        for triangle in combinations(range(n), 3):
            interior = [slot(u, v) for u, v in combinations(triangle, 2)]
            interior_mask = sum(1 << i for i in interior)
            outside = sorted(set(range(n)) - set(triangle))
            signature = [[slot(u, v) for u in triangle] for v in outside]
            outside_edge = slot(*outside) if n == 5 else None
            parts.append((interior, interior_mask, signature, outside_edge))
        for row in np.flatnonzero(data["order"] == n):
            colors = decode(n, int(data["code"][row]))
            tags = int(data["mask"][row])
            for interior, mask, signature, outside_edge in parts:
                if any(colors[i] != 2 for i in interior):
                    continue
                inner_tags = (tags & mask).bit_count()
                if inner_tags > 2:
                    continue
                outputs = masses[inner_tags]
                if n == 3:
                    outputs["root"][int(row)] += 1
                    continue
                exterior = tags & ~mask
                if n == 4 and exterior.bit_count() == 1:
                    outputs["anchor_repeat"][int(row)] += 1
                if exterior and (outside_edge is None or exterior != (1 << outside_edge)):
                    continue
                signatures = [[colors[i] for i in indices] for indices in signature]
                counts = [sum(c > 0 for c in ss) for ss in signatures]
                singletons = [ss.index(2) if size == 1 and 2 in ss else None
                              for ss, size in zip(signatures, counts)]
                if n == 4:
                    outputs["multiple"][int(row)] += int(counts[0] >= 2)
                    outputs["any_single"][int(row)] += int(counts[0] == 1)
                    outputs["blue_single"][int(row)] += int(counts[0] == 1 and 1 in signatures[0])
                    outputs["red_single"][int(row)] += int(singletons[0] is not None)
                    outputs["exceptional"][int(row)] += int(
                        counts[0] >= 2 or (counts[0] == 1 and 1 in signatures[0]))
                    continue
                if not exterior and singletons[0] is not None and singletons[0] == singletons[1]:
                    outputs["red_single_square"][int(row)] += 2
                if colors[outside_edge] == 2:
                    outputs["multiple_marked_degree"][int(row)] += sum(size >= 2 for size in counts)
                    outputs["exceptional_marked_degree"][int(row)] += sum(
                        size >= 2 or (size == 1 and 1 in ss)
                        for size, ss in zip(counts, signatures))
                    outputs["mark_signature_two"][int(row)] += int(sum(counts) == 2)
                elif colors[outside_edge] == 1 and not exterior:
                    outputs["blue_incidence_loss"][int(row)] += sum(counts)

    def sparse(items):
        nonzero = [(i, v) for i, v in items.items() if v]
        positions = [i for i, _ in nonzero]
        values = [v for _, v in nonzero]
        return csr_matrix((values, ([0] * len(values), positions)),
                          shape=(1, len(data["order"])), dtype=np.int64)

    # The three separate Ore bounds with u=3−sum b_i/D imply
    # M ≤ 3 β + (1/2 + 2 β)u + βu².
    quantum = 10000
    eligible = [F(i, quantum) for i in range(quantum+1)
                if 3*beta + (F(1, 2)+2*beta)*F(i, quantum) + beta*F(i, quantum)**2 <= mass_lower]
    lower_defect = max(eligible, default=F(0))
    rows = []
    for terms in masses.values():
        root, w, h, blue, red, red2, single, exceptional, exceptional_degree, j, m2, blue_loss = (
            sparse(terms[name]) for name in ("root", "multiple", "multiple_marked_degree",
                                             "blue_single", "red_single", "red_single_square",
                                             "any_single", "exceptional", "exceptional_marked_degree",
                                             "anchor_repeat", "mark_signature_two", "blue_incidence_loss")
        )
        deficiency = F(mass_lower) - F(309, 250)
        exceptional_deficiency = F(mass_lower) - F(1233, 1000)
        rows.extend((
            ((deficiency, root), (-F(1), w), (-4*beta, blue)),
            ((deficiency, root), (-F(1), h), (-4*beta, blue)),
            ((F(1), red), (lower_defect-3, root)),
            ((F(mass_lower)-12*beta, root), (-F(1), h), (4*beta, red), (-beta, red2)),
            ((3*(F(mass_lower)-4*beta), root), (-3, h), (-F(1), single),
             (4*beta, red), (-beta, red2)),
        ))
        if stronger:
            rows.extend((
                ((exceptional_deficiency, root), (-F(1), exceptional)),
                ((exceptional_deficiency, root), (-F(1), exceptional_degree)),
                ((3*(F(mass_lower)-1), root), (F(1), j), (F(1), blue_loss), (-F(1), m2)),
            ))
    return rows


def k4_neighbor_floor(data, mass_lower):
    """Untyped sixth-order lower row on edges among the K4 high signatures."""
    import numpy as np
    from scipy.sparse import csr_matrix

    gap = F(mass_lower) - F(5, 4)
    assert 0 < gap <= F(1, 20)
    size = len(data["order"])
    parent = np.zeros(size, dtype=np.int64)
    extension = np.zeros(size, dtype=np.int64)
    for row in np.flatnonzero((data["order"] == 4) & (data["mask"] == 0)):
        parent[row] = int(all(c == 2 for c in decode(4, int(data["code"][row]))))
    assert parent.sum() == 1
    pairs = tuple(edge_pairs(6))
    slots = {pair: j for j, pair in enumerate(pairs)}
    splits = []
    for x, y in pairs:
        A = tuple(i for i in range(6) if i not in (x, y))
        base = tuple(slots[edge] for edge in combinations(A, 2))
        first = tuple(slots[min(i, x), max(i, x)] for i in A)
        second = tuple(slots[min(i, y), max(i, y)] for i in A)
        splits.append((slots[x, y], base, first, second))
    for row in np.flatnonzero((data["order"] == 6) & (data["mask"] == 0)):
        colors = decode(6, int(data["code"][row]))
        extension[row] = 2 * sum(
            colors[xy] > 0 and all(colors[j] == 2 for j in base)
            and 2 <= sum(colors[j] > 0 for j in first) <= 3
            and 2 <= sum(colors[j] > 0 for j in second) <= 3
            for xy, base, first, second in splits
        )
    return ((F(32, 5)*gap**3, csr_matrix(parent)), (-F(1), csr_matrix(extension)))
