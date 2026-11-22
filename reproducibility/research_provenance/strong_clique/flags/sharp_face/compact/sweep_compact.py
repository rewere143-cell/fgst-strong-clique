#!/usr/bin/env python3
"""Cache the audited model and search coarser exact C5-face certificates.

Every output stays in compact/. Numerical computations choose approximations;
all reported passes use exact integer/rational coefficient arithmetic.
"""
from __future__ import annotations
import itertools
import json
import lzma
import math
import pickle
from pathlib import Path
import sys
import time
from fractions import Fraction

import numpy as np
from sympy import Matrix

HERE = Path(__file__).resolve().parent
FACE = HERE.parent
BASE = FACE.parent
sys.path[:0] = [str(FACE), str(BASE), str(BASE / 'solver')]
from c5_face_helpers import round_kernel_factor, project_to_kernel
from rooted_order6 import build
from native_scs import smat


def rounded_gram(vectors, size):
    if not vectors:
        return np.zeros((size, size), dtype=object)
    bound = max(abs(v) for row in vectors for v in row)
    dtype = np.int64 if len(vectors) * bound**2 < 2**63 else object
    E = np.array(vectors, dtype=dtype).reshape(-1, size)
    return (E.T @ E).astype(object)


def contribution(model, grams, res, raw, sign=-1):
    for Q, (_, m, K, D) in zip(grams, model['blocks']):
        for row, value in enumerate(Q.flat):
            value = int(value)
            if not value:
                continue
            raw += value * int(K.flat[row])
            for k in range(D.indptr[row], D.indptr[row+1]):
                res[int(D.indices[k])] += sign * value * int(D.data[k])
    return raw


def prepare(prefix):
    cache_path = HERE / f'{prefix}_model_cache.pickle'
    compressed_cache_path = cache_path.with_suffix('.pickle.xz')
    if compressed_cache_path.exists():
        with lzma.open(compressed_cache_path, 'rb') as file:
            cache = pickle.load(file)
        print('reusing losslessly compressed compact model cache', flush=True)
        return cache
    if cache_path.exists():
        with cache_path.open('rb') as file:
            cache = pickle.load(file)
        print('reusing compact model cache', flush=True)
        return cache
    model = build(gram=True)
    face = json.loads((FACE / 'c5_face_data.json').read_text())
    src = json.loads((FACE / 'projected_native_dual.json').read_text())
    support = src['support']
    y = np.load(BASE / f'{prefix}.npz')['y']
    A = model['A'].astype(np.int64)
    N = len(model['variables'])
    neq = len(model['rhs'])
    offset = neq + N
    float_factors = []
    for j, (_, m, K, D) in enumerate(model['blocks']):
        Q = smat(y[offset:offset+m*(m+1)//2], m)
        offset += m*(m+1)//2
        eigenvalues, eigenvectors = np.linalg.eigh((Q+Q.T)/2)
        for h in np.flatnonzero(eigenvalues > 1e-14):
            vector = project_to_kernel(eigenvectors[:, h] * np.sqrt(eigenvalues[h]), face['blocks'][j])
            float_factors.append((j, vector))
    assert offset == len(y)
    Z = []
    for row in src['support_left_nullspace']:
        values = list(map(Fraction, row))
        denominator = math.lcm(*(v.denominator for v in values))
        Z.append([int(v*denominator) for v in values])
    assert len(Z) == 2
    coeff = []
    for _, m, K, D in model['blocks']:
        coeff.append([[(i//m, i%m, int(v)) for i, v in enumerate(np.asarray(D[:, support] @ np.array(z, dtype=np.int64)).reshape(-1)) if v] for z in Z])
    AS = Matrix(A[:, support].T.toarray().tolist())
    pivots = src['support_degree_pivot_rows']
    B = AS[:, pivots]
    _, rows = B.T.rref()
    Cinv = B[list(rows), :].inv()
    CSC = A.tocsc()
    parent = []
    for row in range(A.shape[0]):
        negatives = [int(A.indices[z]) for z in range(A.indptr[row], A.indptr[row+1]) if A.data[z] < 0]
        parent.append(negatives[0] if len(negatives) == 1 else None)
    choices = [[] for _ in range(N)]
    for i, (n, colors) in enumerate(model['variables']):
        if n < 4 or 1 not in colors:
            continue
        for z in range(CSC.indptr[i], CSC.indptr[i+1]):
            row, c = int(CSC.indices[z]), int(CSC.data[z])
            j = parent[row]
            if c > 0 and j is not None and model['variables'][j][0] == n-1 and 1 in model['variables'][j][1]:
                choices[i].append((c, row, j))
    cache = dict(model=model, face=face, src=src, y=y, A=A, support=support,
                Z=Z, coeff=coeff, float_factors=float_factors,
                pivots=pivots, B=B, rows=rows, Cinv=Cinv, choices=choices)
    with lzma.open(compressed_cache_path, 'wb', preset=6) as file:
        pickle.dump(cache, file, protocol=pickle.HIGHEST_PROTOCOL)
    return cache


def choose_pair(F, u, strategy=0):
    """Find well-conditioned independent factors, then fit them exactly."""
    active = [i for i, f in enumerate(F) if any(f)]
    ranked = []
    for i, j in itertools.combinations(active, 2):
        a, c = F[i]
        b, d = F[j]
        determinant = a*d-b*c
        if not determinant:
            continue
        first = Fraction(u[0]*d-b*u[1], determinant)
        second = Fraction(a*u[1]-u[0]*c, determinant)
        if min(first, second) < -1:
            continue
        # Minimize the largest relative factor-weight change.
        score = max(abs(first), abs(second))
        ranked.append((score, i, j, first, second))
    ranked.sort(key=lambda item: (item[0], abs(item[3])+abs(item[4])))
    if not ranked:
        raise AssertionError('no nonnegative exact two-factor fit')
    score, i, j, first, second = ranked[strategy]
    denominator = math.lcm(first.denominator, second.denominator)
    delta = [0] * len(F)
    delta[i], delta[j] = int(first*denominator), int(second*denominator)
    assert all(sum(f[k]*v for f, v in zip(F, delta)) == denominator*u[k] for k in range(2))
    return denominator, delta, dict(factor_indices=[i, j], relative_changes=[str(first), str(second)], max_relative_change=float(score), feasible_pair_count=len(ranked))


def simple_fit(cache, u):
    """Try adding two sparse exact kernel squares rather than reweighting.

    Integer kernel basis columns and their pairwise sums/differences supply
    small exact generators. Only directions with a nonzero support effect
    matter. Their two compatibility coefficients usually are tiny integers.
    """
    data = np.load(FACE / 'c5_face_data.npz')
    generators = []
    seen = set()
    for block in cache['face']['blocks']:
        j = block['block']
        if not any(cache['coeff'][j]):
            continue
        E = data[f'E_{j:03d}']
        active = block['active_coordinates']
        columns = [E[:, k] for k in range(E.shape[1]) if np.any(E[active, k])]
        candidates = columns + [a+s*b for a, b in itertools.combinations(columns, 2) for s in (-1, 1)]
        for vector in candidates:
            v = [int(x) for x in vector]
            common = math.gcd(*v)
            if common:
                v = [x//common for x in v]
            first = next((x for x in v if x), 1)
            if first < 0:
                v = [-x for x in v]
            key = j, tuple(v)
            if key in seen:
                continue
            seen.add(key)
            F = [sum(c*v[a]*v[b] for a, b, c in row) for row in cache['coeff'][j]]
            if any(F):
                generators.append((dict(block=j, vector=v), F))
    ranked = []
    for i, j in itertools.combinations(range(len(generators)), 2):
        a, c = generators[i][1]
        b, d = generators[j][1]
        determinant = a*d-b*c
        if not determinant:
            continue
        first = Fraction(u[0]*d-b*u[1], determinant)
        second = Fraction(a*u[1]-u[0]*c, determinant)
        if min(first, second) < 0:
            continue
        # Prefer the least trace added to the Gram matrices.
        trace = first*sum(x*x for x in generators[i][0]['vector']) + second*sum(x*x for x in generators[j][0]['vector'])
        ranked.append((trace, i, j, first, second))
    assert ranked, ('no nonnegative simple-kernel correction', u, [g[1] for g in generators])
    ranked.sort()
    trace, i, j, first, second = ranked[0]
    denominator = math.lcm(first.denominator, second.denominator)
    extra = [generators[i][0], generators[j][0]]
    weights = [int(first*denominator), int(second*denominator)]
    assert all(sum(generators[l][1][k]*v for l, v in zip((i,j), weights)) == denominator*u[k] for k in range(2))
    return extra, denominator, weights, dict(generator_indices=[i,j], added_weights=[str(first), str(second)], generator_support_effects=[generators[i][1],generators[j][1]], generator_count=len(generators), feasible_pair_count=len(ranked))


def expand_absorption_choices(cache):
    """Use every zero-C5 lower-order parent, including marked triangles.

    This is justified directly by the audited degree row and the exact C5
    vector; it does not introduce any new inequality into the certificate.
    """
    p, A = cache['model'], cache['A']
    X = np.load(FACE / 'c5_face_data.npz')['X']
    CSC = A.tocsc()
    parent = []
    for row in range(A.shape[0]):
        negatives = [int(A.indices[z]) for z in range(A.indptr[row], A.indptr[row+1]) if A.data[z] < 0]
        parent.append(negatives[0] if len(negatives) == 1 else None)
    choices = [[] for _ in p['variables']]
    for i, (n, colors) in enumerate(p['variables']):
        if n < 4 or X[i]:
            continue
        for z in range(CSC.indptr[i], CSC.indptr[i+1]):
            row, c = int(CSC.indices[z]), int(CSC.data[z])
            j = parent[row]
            if c > 0 and j is not None and p['variables'][j][0] == n-1 and X[j] == 0:
                choices[i].append((c, row, j))
    cache['choices_all_defects'] = choices
    return choices


def change_source(cache, prefix):
    cache = dict(cache)
    p = cache['model']
    y = np.load(BASE / f'{prefix}.npz')['y']
    offset = len(p['rhs']) + len(p['variables'])
    factors = []
    for j, (_, m, K, D) in enumerate(p['blocks']):
        Q = smat(y[offset:offset+m*(m+1)//2], m)
        offset += m*(m+1)//2
        ev, V = np.linalg.eigh((Q+Q.T)/2)
        for h in np.flatnonzero(ev > 1e-14):
            factors.append((j, project_to_kernel(V[:,h]*np.sqrt(ev[h]), cache['face']['blocks'][j])))
    assert offset == len(y)
    cache['y'], cache['float_factors'], cache['source'] = y, factors, prefix
    return cache


def attempt(cache, R, pair_strategy=0, simple=False, all_defects=False):
    started = time.time()
    p, face, A = cache['model'], cache['face'], cache['A']
    support, Z = cache['support'], cache['Z']
    choices = (cache.get('choices_all_defects') or expand_absorption_choices(cache)) if all_defects else cache['choices']
    T = R*R
    factors = []
    by_block = [[] for _ in p['blocks']]
    for j, v in cache['float_factors']:
        a = round_kernel_factor(v, face['blocks'][j], R, project=False)
        if any(a):
            factors.append(dict(block=j, vector=a))
            by_block[j].append(a)
    grams = [rounded_gram(vectors, m) for vectors, (_, m, _, _) in zip(by_block, p['blocks'])]
    lam = [round(Fraction(str(float(v)))*T) for v in cache['y'][:len(p['rhs'])]]
    res = [-int(Fraction(str(float(v)))*T) for v in p['obj']]
    raw = 0
    for i, value in enumerate(lam):
        raw += value*int(p['rhs'][i])
        for z in range(A.indptr[i], A.indptr[i+1]):
            res[int(A.indices[z])] += value*int(A.data[z])
    raw = contribution(p, grams, res, raw)
    F = []
    for f in factors:
        v = f['vector']
        F.append([sum(c*v[a]*v[b] for a, b, c in row) for row in cache['coeff'][f['block']]])
    u = [sum(z[i]*res[s] for i, s in enumerate(support)) for z in Z]
    if simple:
        extra, Qden, extra_weights, fit = simple_fit(cache, u)
        original_count = len(factors)
        factors += extra
        weights = [Qden]*original_count + extra_weights
        delta = [0]*original_count + extra_weights
    else:
        Qden, delta, fit = choose_pair(F, u, pair_strategy)
        weights = [Qden+d for d in delta]
    assert min(weights) >= 0
    deltaQ = [np.zeros(M.shape, dtype=object) for M in grams]
    for f, d in zip(factors, delta):
        if d:
            v = np.array(f['vector'], dtype=object)
            deltaQ[f['block']] += d*np.outer(v, v)
    res = [v*Qden for v in res]
    raw *= Qden
    lam = [v*Qden for v in lam]
    T *= Qden
    raw = contribution(p, deltaQ, res, raw)
    dlam = cache['Cinv'] * Matrix([-res[support[i]] for i in cache['rows']])
    assert cache['B']*dlam == Matrix([-res[s] for s in support])
    L = math.lcm(*(int(v.q) for v in dlam))
    res = [v*L for v in res]
    raw *= L
    lam = [v*L for v in lam]
    weights = [v*L for v in weights]
    Qden *= L
    T *= L
    for i, dl in zip(cache['pivots'], dlam):
        value = int(dl*L)
        lam[i] += value
        raw += value*int(p['rhs'][i])
        for z in range(A.indptr[i], A.indptr[i+1]):
            res[int(A.indices[z])] += value*int(A.data[z])
    assert all(res[s] == 0 for s in support)
    assert Fraction(raw, T) == Fraction(5, 4)
    before_absorption = sum(v < 0 for v in res)
    transfers = []
    for order in (6, 5, 4):
        for i, (n, colors) in enumerate(p['variables']):
            if n != order or res[i] >= 0 or not choices[i]:
                continue
            c, row, parent = max(choices[i], key=lambda item: (item[0], res[item[2]]))
            d = -Fraction(res[i], c)
            assert d > 0 and p['rhs'][row] == 0
            lam[row] += d
            for z in range(A.indptr[row], A.indptr[row+1]):
                res[int(A.indices[z])] += d*int(A.data[z])
            assert res[i] == 0
            transfers.append(dict(child=i, parent=parent, degree_row=row, child_coefficient=c))
    clearing = math.lcm(*(Fraction(v).denominator for v in lam))
    lam = [int(Fraction(v)*clearing) for v in lam]
    res = [int(Fraction(v)*clearing) for v in res]
    weights = [v*clearing for v in weights]
    raw *= clearing
    Qden *= clearing
    T *= clearing
    common = math.gcd(Qden, math.gcd(*weights))
    common = math.gcd(common, math.gcd(*lam))
    common = math.gcd(common, math.gcd(*res))
    if common > 1:
        Qden //= common
        T //= common
        raw //= common
        weights = [v//common for v in weights]
        lam = [v//common for v in lam]
        res = [v//common for v in res]
    assert all(res[s] == 0 for s in support)
    assert raw*4 == T*5 and T == Qden*R*R
    negatives = {str(i): str(-v) for i, v in enumerate(res) if v < 0}
    correction = sum(map(int, negatives.values()))
    summary = dict(vector_denominator=R, pair_strategy=pair_strategy,
                   exact_sharp_pass=not negatives, factor_count=len(factors),
                   factor_nonzero_entries=sum(bool(v) for f in factors for v in f['vector']),
                   weight_denominator_digits=len(str(Qden)), common_denominator_digits=len(str(T)),
                   max_vector_numerator=max(abs(v) for f in factors for v in f['vector']),
                   zero_residuals=sum(v == 0 for v in res),
                   before_absorption_negative_count=before_absorption,
                   defect_transfers=len(transfers), negative_residual_count=len(negatives),
                   negative_defect_free_count=sum(res[i] < 0 and 1 not in c for i, (_, c) in enumerate(p['variables'])),
                   correction=str(Fraction(correction, T)),
                   degree3_residuals=[str(Fraction(v, T)) for v in res[:5]],
                   two_factor_fit=fit, seconds=time.time()-started)
    summary['correction_method'] = 'add_two_sparse_kernel_factors' if simple else 'reweight_two_native_factors'
    summary['absorb_all_zero_C5_parents'] = all_defects
    stem = f'compact_R{R}_simple' if simple else f'compact_R{R}_pair{pair_strategy}'
    if all_defects:
        stem += '_fourdefects'
    if cache.get('source', 'native_sdp_01') != 'native_sdp_01':
        stem = cache['source']+'_'+stem
    if negatives:
        summary['negative_obstructions'] = [dict(index=i, order=p['variables'][i][0], colors=list(p['variables'][i][1]), coefficient=str(Fraction(v, T))) for i, v in enumerate(res) if v < 0]
    else:
        out = dict(claim='Exact arithmetic candidate; independent audit still required.',
                   rational_bound='5/4', rational_bound_decimal=1.25, raw_dual_value='5/4',
                   rounding_correction='0', common_denominator=str(T),
                   weight_denominator=Qden, vector_denominator=R, variables=len(res),
                   equations=len(lam), psd_blocks=len(grams), nonzero_rank_one_factors=len(factors),
                   negative_residual_count=0, all_positive_C5_residuals_zero=True,
                   all_PSD_factors_annihilate_C5=True,
                   degree_weights_numerators={n: str(v) for n, v in zip(p['names'], lam) if v},
                   rank_one_factors=[dict(block=f['block'], weight_numerator=mu, vector_numerators=f['vector']) for f, mu in zip(factors, weights) if mu],
                   negative_residual_numerators={}, sharp_5_over_4=True,
                   two_factor_fit=fit, defect_absorption_transfers=transfers)
        (HERE / f'{stem}_certificate.json').write_text(json.dumps(out, indent=2)+'\n')
        summary['certificate'] = f'{stem}_certificate.json'
    (HERE / f'{stem}_result.json').write_text(json.dumps(summary, indent=2)+'\n')
    print(json.dumps({k: v for k, v in summary.items() if k != 'negative_obstructions'}, indent=2), flush=True)
    return summary


def main():
    prefix = 'native_sdp_01'
    scales = [int(x) for x in sys.argv[1:]] or [10**4, 10**5, 10**6, 10**8]
    cache = prepare(prefix)
    results = []
    for R in scales:
        results.append(attempt(cache, R))
        (HERE / 'sweep_results.json').write_text(json.dumps(results, indent=2)+'\n')


if __name__ == '__main__':
    main()
