"""Explore affine changes to degree multipliers with projected PSD fixed.

This is a numerical search, not a certificate. The default C5-only test
keeps a subset of the necessary coefficient constraints.
"""

from array import array
from collections import Counter
from fractions import Fraction
from itertools import combinations, permutations
from math import lcm
from pathlib import Path
import argparse
import json
import sys
import time

from multigraph_lift_probe import c5_orbits, decode, edge_pairs, encode, find_simple_residuals, read_ints


def forest(edges, mask, n):
    roots = list(range(n))
    for i, (u, v) in enumerate(edges):
        if not (mask >> i & 1):
            continue
        while roots[u] != u:
            u = roots[u]
        while roots[v] != v:
            v = roots[v]
        if u == v:
            return False
        roots[u] = v
    return True


def build(base, certificate_path, face_only, boolean, profiles, monomials,
          multiplier_degree=None, test_degree=None, progress=False,
          vary_plain=False, tagged_gram=False, scale_plain_gram=False,
          extension_grid=(), free_extension=False, extension_moments=False,
          record_metadata=False, retain_zero_rows=False, variable_metadata=None):
    import numpy as np
    from scipy.sparse import coo_matrix

    data = base / "audit" / "flag_coefficients"
    ids = {n: read_ints(data / f"idx{n}.bin", "i") for n in range(3, 6)}
    ids[6] = read_ints(base / "flags" / "order6_orbit_index.bin", "i")
    ids[6] = array("i", (value + 728 if value >= 0 else value for value in ids[6]))
    certificate = json.loads(certificate_path.read_text())
    old_scale, baseline_residual, legacy_rows, plain_root, plain_gram = find_simple_residuals(
        certificate, data, ids
    )
    extension_grid = tuple(map(Fraction, extension_grid))
    if extension_moments:
        assert len(extension_grid) >= 2 and tuple(sorted(set(extension_grid))) == extension_grid
    extension_scaling = lcm(1, *(alpha.denominator**2 for alpha in extension_grid))
    scale = old_scale * extension_scaling
    if extension_scaling != 1:
        baseline_residual = [value * extension_scaling for value in baseline_residual]
        plain_root *= extension_scaling
        plain_gram = [value * extension_scaling for value in plain_gram]
        for key, row in legacy_rows.items():
            legacy_rows[key] = [(u, value * extension_scaling) for u, value in row]

    c5 = c5_orbits(ids)
    selected = dict(c5) if face_only else {}
    if not face_only:
        for n in range(3, 7):
            for code, variable in enumerate(ids[n]):
                if variable >= 0:
                    selected.setdefault((n, variable), code)
    selected[(2, -1)] = 0
    grouped = {(n, code): idx for (n, idx), code in selected.items()}
    pairs_by_order = {n: edge_pairs(n) for n in range(2, 7)}
    marked = {
        (n, code): tuple(i for i, color in enumerate(decode(n, code)) if color == 2)
        for n, code in grouped
    }
    permutations_by_order = {n: tuple(permutations(range(n))) for n in range(2, 7)}
    permuted_pair_labels = {}
    permuted_pair_indices = {}
    needed_prefixes = {}
    for n in range(3, 7):
        pair_index = {pair: i for i, pair in enumerate(pairs_by_order[n])}
        permuted_pair_labels[n] = tuple(
            tuple(tuple(sorted((perm[i], perm[j]))) for i, j in pairs_by_order[n])
            for perm in permutations_by_order[n]
        )
        permuted_pair_indices[n] = np.array(
            [[pair_index[pair] for pair in projection] for projection in permuted_pair_labels[n]],
            dtype=np.intp,
        )
        needed_prefixes[n] = np.zeros(3 ** (len(pairs_by_order[n - 1]) - 1), dtype=bool)
        for k, code in marked.keys() | legacy_rows.keys():
            if k == n - 1:
                needed_prefixes[n][code] = True

    # The correction degree multiplier for each labeled chosen support T,
    # attachment u, and support marked edge e has variable component z[T,u,e].
    # One representative per support orbit suffices because all its attach
    # labels and its marks may carry separate multipliers.
    multiplier_indices = {}
    root_terms = Counter()
    for n, code in sorted(grouped):
        if n > 5:
            continue
        local_mark_pairs = tuple(pairs_by_order[n][i] for i in marked[n, code])
        for u in range(n):
            decoration_indices = range(
                0 if vary_plain else 1, 1 << len(marked[n, code])
            ) if profiles else marked[n, code]
            for e in decoration_indices:
                if monomials and (
                    (multiplier_degree is not None and e.bit_count() > multiplier_degree)
                    or not forest(local_mark_pairs, e, n)
                ):
                    continue
                if profiles and not monomials and test_degree is not None and e.bit_count() > test_degree:
                    continue
                idx = len(multiplier_indices)
                multiplier_indices[n, code, u, e] = idx
                if n == 2 and (not vary_plain or e):
                    root_terms[idx] += 1

    assert not (vary_plain or tagged_gram or scale_plain_gram or extension_grid or free_extension) or profiles
    assert not (extension_grid and free_extension)
    assert not free_extension or (monomials and test_degree == 1)
    correction_count = len(multiplier_indices)
    if variable_metadata is not None:
        variable_metadata.extend(multiplier_indices)
    if tagged_gram or extension_grid or free_extension:
        from multigraph_tagged_gram import TaggedGram
        gram = TaggedGram(data, certificate_path)
        assert gram.scale == old_scale
    else:
        gram = None
    n_tagged_psd = gram.block_count if tagged_gram else 0
    plain_gram_col = correction_count + n_tagged_psd if scale_plain_gram else None
    extension_start = correction_count + n_tagged_psd + int(scale_plain_gram)
    n_extension_blocks = gram.block_count if extension_grid or free_extension else 0
    n_extension_choices = 2 if extension_moments else (
        len(extension_grid) if extension_grid else int(free_extension)
    )
    column_count = extension_start + n_extension_blocks * n_extension_choices
    extension_mult = tuple(
        (int(alpha * extension_scaling), int(alpha**2 * extension_scaling))
        for alpha in extension_grid
    )

    rows = array("i")
    cols = array("i")
    values = array("d")
    rhs = array("d")
    exact_rhs = []
    row_meta = []
    active_order = array("b")
    active_face = array("b")
    active_tag_size = array("b")
    on_face = False

    exact_values = array("q")

    def add_row(coefs, threshold, description, fractional=None):
        terms = [(k, int(v) * scale) for k, v in coefs.items() if v]
        if fractional:
            terms.extend((k, int(v)) for k, v in fractional.items() if v)
        if not retain_zero_rows and not terms and threshold <= 0:
            return
        for k, v in terms:
            rows.append(len(rhs))
            cols.append(k)
            values.append(v / scale)
            exact_values.append(-v)
        rhs.append(threshold / scale)
        exact_rhs.append(-threshold)
        active_order.append(description[0])
        active_face.append(on_face)
        active_tag_size.append(len(description[2]))
        if face_only or record_metadata:
            row_meta.append(description)

    # Root residual C b_01 - (sum z_2,u,01) b_01 is nonnegative iff
    # sum z_2,u,01 <= C. Save this row for interpretation only, optimize C.
    if vary_plain or scale_plain_gram:
        on_face = True
        plain_root_degree = (
            {multiplier_indices[2, 0, u, 0]: -1 for u in range(2)} if vary_plain else {}
        )
        add_row(plain_root_degree, -plain_root if scale_plain_gram else 0,
                (2, 0, ()), {plain_gram_col: -plain_root} if scale_plain_gram else None)
    if extension_moments:
        # PSD [[plain_scale, alpha_mean], [alpha_mean, alpha_square_mean]]
        # is enforced by the secant envelope of x -> x^2 on the grid.
        on_face = True
        for block in range(n_extension_blocks):
            mean = extension_start + 2 * block
            square = mean + 1
            low, high = extension_grid[0], extension_grid[-1]
            for a, b in ((Fraction(1), low), (Fraction(-1), -high)):
                coeff = {mean: int(a)}
                if scale_plain_gram:
                    add_row(coeff, 0, (2, 0, ()), {plain_gram_col: -int(b * scale)})
                else:
                    add_row(coeff, int(b * scale), (2, 0, ()))
            for a, b in zip(extension_grid, extension_grid[1:]):
                fraction = {mean: -int((a + b) * scale)}
                if scale_plain_gram:
                    fraction[plain_gram_col] = int(a * b * scale)
                add_row({square: 1}, 0 if scale_plain_gram else -int(a * b * scale),
                        (2, 0, ()), fraction)
    elif extension_grid:
        on_face = True
        for block in range(n_extension_blocks):
            row = {
                extension_start + block * n_extension_choices + j: -1
                for j in range(n_extension_choices)
            }
            if scale_plain_gram:
                row[plain_gram_col] = 1
            add_row(row, 0 if scale_plain_gram else -scale, (2, 0, ()))

    for support_counter, ((n, code), idx) in enumerate(sorted(grouped.items())):
        if n == 2:
            continue
        on_face = (n, idx) in c5
        if progress and support_counter % 2000 == 0:
            print(f"support {support_counter}/{len(grouped)}, constraints {len(rhs)}", file=sys.stderr, flush=True)
        P = pairs_by_order[n]
        original = decode(n, code)
        colors = dict(zip(P, original))
        old_marks = tuple(P[i] for i in marked[n, code])
        linear = {e: Counter() for e in old_marks}
        rhs_linear = Counter()
        quadratic = {}
        rhs_quadratic = Counter()
        prefix = tuple(i for i, pair in enumerate(P) if pair[1] < n - 1)
        aut = 0
        profile_extensions = []
        profile_parent_perms = []
        aut_marker_perms = []
        old_mark_indices = {e: index for index, e in enumerate(old_marks)}
        pair_index = {e: index for index, e in enumerate(P)}

        permuted = np.asarray(original, dtype=np.intp)[permuted_pair_indices[n]]
        parent_code_vector = permuted[:, prefix[1:]] @ np.array(
            [3**i for i in range(len(prefix) - 1)], dtype=np.intp
        )
        is_aut = np.all(permuted == original, axis=1)
        aut = int(np.count_nonzero(is_aut))
        needed = is_aut | needed_prefixes[n][parent_code_vector]
        if n == 4:
            needed |= permuted[:, -1] == 2
        needed &= permuted[:, 0] == 2
        if tagged_gram:
            gram_terms = gram.coefficients(n, permuted, permuted_pair_indices[n])
        if extension_grid or free_extension:
            extension_linear, extension_quadratic = gram.extension_coefficients(
                n, permuted, permuted_pair_indices[n]
            )

        def tagged_gram_row(tag):
            result = {}
            if tagged_gram and len(tag) == 1:
                result.update({
                    correction_count + j: -int(v) * extension_scaling
                    for j, v in enumerate(gram_terms[pair_index[tag[0]]])
                    if v
                })
            if free_extension and len(tag) == 1:
                result.update({
                    extension_start + j: -int(v)
                    for j, v in enumerate(extension_linear[pair_index[tag[0]]])
                    if v
                })
            if extension_grid and len(tag) in (1, 2):
                if len(tag) == 1:
                    line = extension_linear[pair_index[tag[0]]]
                else:
                    e, f = sorted(pair_index[pair] for pair in tag)
                    line = extension_quadratic[e, f]
                if extension_moments:
                    for block, value in enumerate(line):
                        if value:
                            result[extension_start + 2 * block + len(tag) - 1] = (
                                -int(value) * extension_scaling
                            )
                else:
                    for block, value in enumerate(line):
                        if value:
                            for j, weights in enumerate(extension_mult):
                                result[extension_start + block * n_extension_choices + j] = (
                                    -int(value) * weights[len(tag) - 1]
                                )
            return result or None

        for perm_num in np.flatnonzero(needed):
            perm = permutations_by_order[n][perm_num]
            projected_edges = permuted_pair_labels[n][perm_num]
            base_code = int(parent_code_vector[perm_num])
            is_parent_representative = bool(is_aut[perm_num])
            base_marks = marked.get((n - 1, base_code))
            if n == 4 and permuted[perm_num, -1] == 2:
                # Objective increase (b_e + b_f + b_e b_f)/2 per labeled order.
                e, f = projected_edges[0], projected_edges[-1]
                rhs_linear[e] += scale // 2
                rhs_linear[f] += scale // 2
                rhs_quadratic[tuple(sorted((e, f)))] += scale // 2

            for u, old_weight in legacy_rows[n - 1, base_code]:
                attached = tuple(sorted((perm[u], perm[-1])))
                if colors[attached] == 2:
                    rhs_linear[attached] -= old_weight

            if base_marks is not None and profiles:
                parent_indices = tuple(old_mark_indices[projected_edges[prefix[e]]] for e in base_marks)
                attachments = []
                for u in range(n - 1):
                    attached = tuple(sorted((perm[u], perm[-1])))
                    if colors[attached]:
                        attachments.append((u, old_mark_indices.get(attached)))
                parent_cover = sum(1 << edge for edge in parent_indices)
                profile_extensions.append((base_code, parent_indices, parent_cover, attachments))
            elif base_marks is not None:
                for u in range(n - 1):
                    attached = tuple(sorted((perm[u], perm[-1])))
                    w = colors[attached]
                    if not w:
                        continue
                    for e in base_marks:
                        variable = multiplier_indices[n - 1, base_code, u, e]
                        flagged_edge = projected_edges[prefix[e]]
                        linear[flagged_edge][variable] += 1
                        if w == 2:
                            pair = tuple(sorted((attached, flagged_edge)))
                            quadratic.setdefault(pair, Counter())[variable] += 1

            if n <= 5 and is_parent_representative and profiles:
                profile_parent_perms.append(
                    tuple(old_mark_indices[projected_edges[e]] for e in marked[n, code])
                )
            elif n <= 5 and is_parent_representative:
                for u in range(n):
                    for e in marked[n, code]:
                        variable = multiplier_indices[n, code, u, e]
                        linear[projected_edges[e]][variable] -= 1
            if is_parent_representative and profiles:
                symmetry = tuple(old_mark_indices[projected_edges[e]] for e in marked[n, code])
                if symmetry not in aut_marker_perms:
                    aut_marker_perms.append(symmetry)

        assert aut > 0
        if vary_plain or scale_plain_gram:
            plain = Counter()
            if vary_plain:
                for parent_code, _, _, attachments in profile_extensions:
                    for u, _ in attachments:
                        plain[multiplier_indices[n - 1, parent_code, u, 0]] += 1
                for _ in profile_parent_perms:
                    for u in range(n):
                        plain[multiplier_indices[n, code, u, 0]] -= 1
            raw_plain = plain_gram[idx] * aut if scale_plain_gram else 0
            add_row(
                plain, -baseline_residual[idx] * aut - raw_plain, (n, code, ()),
                {plain_gram_col: -raw_plain} if scale_plain_gram else None,
            )

        if profiles and monomials:
            def masks():
                limit = len(old_marks) if test_degree is None else min(test_degree, len(old_marks))
                for k in range(1, limit + 1):
                    for chosen in combinations(range(len(old_marks)), k):
                        yield sum(1 << e for e in chosen), chosen

            for mask, chosen in masks():
                if not forest(old_marks, mask, n):
                    continue
                if any(sum(1 << sym[e] for e in chosen) < mask for sym in aut_marker_perms):
                    continue
                row = Counter()
                doubled = tuple(old_marks[e] for e in chosen)
                if len(doubled) == 1:
                    threshold = rhs_linear[doubled[0]]
                elif len(doubled) == 2:
                    threshold = rhs_quadratic[tuple(sorted(doubled))]
                else:
                    threshold = 0

                for parent_code, parent_mark_indices, covered, attachments in profile_extensions:
                    missing = mask & ~covered
                    if missing & (missing - 1):
                        continue
                    parent_mask = sum(
                        ((mask >> old_index) & 1) << new_index
                        for new_index, old_index in enumerate(parent_mark_indices)
                    )
                    if not parent_mask and not vary_plain:
                        continue
                    if multiplier_degree is not None and parent_mask.bit_count() > multiplier_degree:
                        continue
                    for u, attach_index in attachments:
                        if missing == 0 or (
                            attach_index is not None and missing == 1 << attach_index
                        ):
                            variable = multiplier_indices[n - 1, parent_code, u, parent_mask]
                            row[variable] += 1
                parent_perms = profile_parent_perms
                if multiplier_degree is not None and len(chosen) > multiplier_degree:
                    parent_perms = []
                for indices in parent_perms:
                    projected_mask = sum(
                        ((mask >> old_index) & 1) << new_index
                        for new_index, old_index in enumerate(indices)
                    )
                    for u in range(n):
                        variable = multiplier_indices[n, code, u, projected_mask]
                        row[variable] -= 1
                add_row(row, threshold, (n, code, doubled), tagged_gram_row(doubled))
        elif profiles:
            for mask in range(1, 1 << len(old_marks)):
                if test_degree is not None and mask.bit_count() > test_degree:
                    continue
                row = Counter()
                threshold = -baseline_residual[idx] * aut
                doubled = tuple(e for index, e in enumerate(old_marks) if mask >> index & 1)
                for e in doubled:
                    threshold += rhs_linear[e]
                for ef in combinations(doubled, 2):
                    threshold += rhs_quadratic[tuple(sorted(ef))]

                for parent_code, parent_mark_indices, _, attachments in profile_extensions:
                    parent_mask = sum(
                        ((mask >> old_index) & 1) << new_index
                        for new_index, old_index in enumerate(parent_mark_indices)
                    )
                    if parent_mask or vary_plain:
                        for u, attach_index in attachments:
                            variable = multiplier_indices[n - 1, parent_code, u, parent_mask]
                            weight = 1 + ((mask >> attach_index) & 1) if attach_index is not None else 1
                            row[variable] += weight
                for indices in profile_parent_perms:
                    projected_mask = sum(
                        ((mask >> old_index) & 1) << new_index
                        for new_index, old_index in enumerate(indices)
                    )
                    for u in range(n):
                        variable = multiplier_indices[n, code, u, projected_mask]
                        row[variable] -= 1
                grams = None
                if gram:
                    grams = Counter()
                    for subset_length in (1, 2):
                        for subset in combinations(doubled, subset_length):
                            grams.update(tagged_gram_row(subset) or {})
                raw_plain = plain_gram[idx] * aut if scale_plain_gram else 0
                if scale_plain_gram:
                    grams = dict(grams or {})
                    grams[plain_gram_col] = -raw_plain
                add_row(row, threshold - raw_plain, (n, code, doubled), grams)
        elif boolean:
            for k in range(1, len(old_marks) + 1):
                for doubled in combinations(old_marks, k):
                    row = Counter()
                    threshold = -baseline_residual[idx] * aut
                    for e in doubled:
                        row.update(linear[e])
                        threshold += rhs_linear[e]
                    for e, f in combinations(doubled, 2):
                        pair = tuple(sorted((e, f)))
                        row.update(quadratic.get(pair, {}))
                        threshold += rhs_quadratic[pair]
                    add_row(row, threshold, (n, code, doubled))
        else:
            for e, terms in linear.items():
                add_row(terms, rhs_linear[e], (n, code, (e,)))
            for pair in quadratic.keys() | rhs_quadratic.keys():
                add_row(quadratic.get(pair, {}), rhs_quadratic[pair], (n, code, pair))

    # Rows have all-support permutation multiplicity on both sides.
    # A matrix row A z >= rhs becomes -A z <= -rhs for linprog.
    coefficients = np.frombuffer(values, dtype=np.float64)
    indices = (np.frombuffer(rows, dtype=np.int32), np.frombuffer(cols, dtype=np.int32))
    matrix = coo_matrix(
        (-coefficients, indices), shape=(len(rhs), column_count),
    ).tocsr()
    numerator_matrix = coo_matrix(
        (np.frombuffer(exact_values, dtype=np.int64), indices), shape=matrix.shape
    ).tocsr()
    objective = np.zeros(column_count)
    objective_exact = np.zeros(column_count, dtype=np.int64)
    restricted = np.zeros(column_count, dtype=bool)
    for idx, value in root_terms.items():
        objective[idx] = value
        objective_exact[idx] = value * scale
    if tagged_gram:
        objective[correction_count:correction_count + n_tagged_psd] = np.asarray(gram.root, dtype=float) / old_scale
        objective_exact[correction_count:correction_count + n_tagged_psd] = np.asarray(
            [value * extension_scaling for value in gram.root], dtype=np.int64
        )
        restricted[correction_count:correction_count + n_tagged_psd] = True
    if scale_plain_gram:
        restricted[plain_gram_col] = True
    if extension_moments:
        restricted[extension_start + 1::2] = True
    elif extension_grid:
        restricted[extension_start:] = True
    return (matrix, -np.frombuffer(rhs, dtype=np.float64), objective, row_meta,
            np.frombuffer(active_order, dtype=np.int8), np.frombuffer(active_face, dtype=np.int8),
            np.frombuffer(active_tag_size, dtype=np.int8), exact_rhs, scale,
            restricted, numerator_matrix, objective_exact)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("snapshot", type=Path)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("--vendor", type=Path)
    parser.add_argument("--full", action="store_true")
    parser.add_argument("--boolean", action="store_true", help="evaluate at multiplicities 1 and 2")
    parser.add_argument("--profiles", action="store_true", help="independent corrections for each nonzero Boolean profile")
    parser.add_argument("--monomials", action="store_true", help="independent corrections for all square-free monomials")
    parser.add_argument("--multiplier-degree", type=int)
    parser.add_argument("--test-degree", type=int)
    parser.add_argument("--cache", type=Path)
    parser.add_argument("--progress", action="store_true")
    parser.add_argument("--build-only", action="store_true")
    parser.add_argument("--vary-plain", action="store_true")
    parser.add_argument("--tagged-gram", action="store_true")
    parser.add_argument("--scale-plain-gram", action="store_true")
    parser.add_argument("--extension-grid", nargs="+", default=())
    parser.add_argument("--free-extension", action="store_true")
    parser.add_argument("--extension-moments", action="store_true")
    parser.add_argument("--primal-form", action="store_true")
    parser.add_argument("--solver", choices=("highs-ipm", "highs-ds"), default="highs-ipm")
    parser.add_argument("--threads", type=int, default=1)
    parser.add_argument("--candidate", type=Path)
    parser.add_argument("--allowance-cap", type=float)
    parser.add_argument("--limit-seconds", type=int, default=120)
    args = parser.parse_args()
    if args.vendor:
        sys.path.insert(0, str(args.vendor))
    from scipy.optimize import linprog

    start = time.monotonic()
    matrix, rhs, objective, _, order, face, tag_size, exact_rhs, scale, restricted, numerator, objective_exact = build(
        args.snapshot, args.certificate, not args.full, args.boolean,
        args.profiles or args.monomials, args.monomials, args.multiplier_degree,
        args.test_degree, args.progress, args.vary_plain, args.tagged_gram, args.scale_plain_gram,
        args.extension_grid, args.free_extension, args.extension_moments
    )
    print(
        json.dumps({"matrix_shape": matrix.shape, "nonzeros": matrix.nnz, "boolean": args.boolean,
                    "profiles": args.profiles, "monomials": args.monomials, "vary_plain": args.vary_plain,
                    "tagged_gram": args.tagged_gram, "scale_plain_gram": args.scale_plain_gram,
                    "extension_grid": args.extension_grid, "free_extension": args.free_extension,
                    "extension_moments": args.extension_moments,
                    "C5_face_only": not args.full, "build_seconds": time.monotonic() - start}),
        file=sys.stderr,
        flush=True,
    )
    if args.cache:
        import numpy as np
        from scipy.sparse import save_npz
        save_npz(args.cache.with_suffix(".npz"), matrix)
        save_npz(args.cache.with_suffix(".exact.npz"), numerator)
        np.savez(args.cache.with_suffix(".extra.npz"), rhs=rhs, objective=objective,
                 order=order, face=face, tag_size=tag_size, scale=np.int64(scale),
                 exact_rhs=np.array(exact_rhs, dtype=np.int64),
                 restricted=restricted, exact_objective=objective_exact,
                 complete=np.bool_(args.full and args.monomials and not args.free_extension and (
                     args.test_degree is None or args.multiplier_degree is not None and
                     args.test_degree >= args.multiplier_degree + 1
                 )))
    if args.build_only:
        return
    options = {"time_limit": args.limit_seconds, "threads": args.threads}
    if args.allowance_cap is not None:
        import numpy as np
        from scipy.sparse import csr_matrix, vstack
        bounds = [(0, None) if flag else (None, None) for flag in restricted]
        result = linprog(
            np.zeros(len(objective)), A_ub=vstack((matrix, csr_matrix(objective)), format="csr"),
            b_ub=np.r_[rhs, args.allowance_cap], bounds=bounds, method=args.solver, options=options,
        )
        target = float(objective @ result.x) if result.success else None
        if args.candidate and result.success:
            np.savez(args.candidate, multipliers=result.x, dual=-result.ineqlin.marginals[:-1])
    elif args.primal_form:
        ineq = -matrix[:, restricted].T.tocsr() if restricted.any() else None
        ineq_rhs = objective[restricted] if restricted.any() else None
        result = linprog(
            rhs, A_eq=matrix[:, ~restricted].T.tocsr(), b_eq=-objective[~restricted],
            A_ub=ineq, b_ub=ineq_rhs, bounds=(0, None), method=args.solver, options=options,
        )
        target = None if result.fun is None else -result.fun
        if args.candidate and result.success:
            import numpy as np
            multipliers = np.zeros(len(restricted))
            multipliers[~restricted] = result.eqlin.marginals
            if restricted.any():
                multipliers[restricted] = -result.ineqlin.marginals
            np.savez(args.candidate, multipliers=multipliers, dual=result.x)
    else:
        bounds = [(0, None) if flag else (None, None) for flag in restricted]
        result = linprog(
            objective, A_ub=matrix, b_ub=rhs, bounds=bounds,
            method=args.solver, options=options,
        )
        target = result.fun
        if args.candidate and result.success:
            import numpy as np
            np.savez(args.candidate, multipliers=result.x, dual=-result.ineqlin.marginals)
    print(
        json.dumps({"C5_face_only": not args.full, "matrix_shape": matrix.shape, "boolean": args.boolean,
                    "profiles": args.profiles, "monomials": args.monomials,
                    "status": result.status, "message": result.message,
                    ("minimum_necessary_root_allowance" if args.allowance_cap is None else
                     "feasible_candidate_allowance"): target,
                    "total_seconds": time.monotonic() - start},
                   indent=2)
    )


if __name__ == "__main__":
    main()
