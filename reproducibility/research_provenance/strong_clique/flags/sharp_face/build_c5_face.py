#!/usr/bin/env python3
"""Persist and verify the exact C5 face of the audited order-six model.

No numerical SDP claim is made.  All generated files stay in this directory.
"""
from __future__ import annotations

import hashlib
import itertools as it
import json
import math
from pathlib import Path
import sys
import time

import numpy as np
from sympy import Matrix

HERE = Path(__file__).resolve().parent
BASE = HERE.parent
sys.path.insert(0, str(BASE))
from rooted_order6 import build
from rooted_order4 import pairs
from rooted_order5 import orbits


def exact_int_array(values):
    """Reject fractional or out-of-range input rather than silently round it."""
    array = np.asarray(values)
    result = array.astype(np.int64)
    assert np.array_equal(array, result)
    return result


def integer_product(left, right):
    """Use int64 only after a rigorous no-overflow bound."""
    assert left.shape[1] == right.shape[0]
    a = max((abs(int(x)) for x in left.flat), default=0)
    b = max((abs(int(x)) for x in right.flat), default=0)
    assert a * b * left.shape[1] < 2**63
    return left @ right


def c5_vector(model):
    """Ordered marked roots and all color-preserving maps, diagonal color 0."""
    variables = model['variables']
    index = {v: i for i, v in enumerate(variables)}
    small = {k: orbits(k) for k in (3, 4, 5)}
    idx6 = np.fromfile(BASE / 'order6_orbit_index.bin', dtype=np.int32)
    offset = sum(n < 6 for n, c in variables)

    def ix(k, c):
        if k < 6:
            return index[k, small[k][2][c]] if c in small[k][2] else None
        q = int(idx6[sum(v * 3**j for j, v in enumerate(c[1:]))])
        return offset + q if q >= 0 else None

    X = np.zeros(len(variables), dtype=np.int64)
    roots = [(u, v) for u in range(5) for v in range(5) if (u-v) % 5 in (1, 4)]
    for k in (3, 4, 5, 6):
        counts = {}
        for u, v in roots:
            for tail in it.product(range(5), repeat=k-2):
                image = (u, v) + tail
                c = tuple(2 if (image[i]-image[j]) % 5 in (1, 4) else 0
                          for i, j in pairs(k))
                if ix(k, c) is not None:
                    counts[c] = counts.get(c, 0) + 1
        # A representative is a single labelled pattern, not an orbit sum.
        for i, (kk, c) in enumerate(variables):
            if kk == k:
                X[i] = counts.get(c, 0) * (160 // (10 * 2**(k-2)))
    return X


def block_face(M):
    """Return exact RREF rows B^T and a denominator-cleared kernel basis E.

    M*v=0 iff R*v=0, where R=B^T and R[:,pivots]=I.
    R=N/denominator. If t is an arbitrary integer vector, v=E*t has
    v[free]=denominator*t and integer pivot entries, with M*v=0 exactly.
    """
    m = len(M)
    symbolic = Matrix(M.tolist())
    full_rref, pivots = symbolic.rref()
    rank = len(pivots)
    pivots = list(pivots)
    free = [i for i in range(m) if i not in pivots]
    R = full_rref[:rank, :]
    denominator = math.lcm(*(int(x.q) for x in R)) if rank else 1
    N = exact_int_array([[int(denominator * R[i, j]) for j in range(m)]
                         for i in range(rank)]).reshape(rank, m)
    E = np.zeros((m, len(free)), dtype=np.int64)
    E[free, np.arange(len(free))] = denominator
    if rank:
        E[pivots, :] = -N[:, free]
    assert np.array_equal(integer_product(M, E), np.zeros((m, len(free)), dtype=np.int64))
    assert np.array_equal(integer_product(N, E), np.zeros((rank, len(free)), dtype=np.int64))
    assert np.array_equal(N[:, pivots], denominator * np.eye(rank, dtype=np.int64))

    # Verify exact PSD and rank using the small principal pivot submatrix.
    # M=M[:,P]*C^-1*M[P,:], C>0; this also proves the row constraints span
    # the full row space and that the independent free coordinates span ker M.
    if rank:
        C = symbolic.extract(pivots, pivots)
        assert C.inv() * symbolic.extract(pivots, range(m)) == R
        assert symbolic == symbolic.extract(range(m), pivots) * R
        _, positive_pivots = C.LDLdecomposition(hermitian=False)
        assert all(positive_pivots[i, i] > 0 for i in range(rank))
        ld = [str(positive_pivots[i, i]) for i in range(rank)]
    else:
        assert not np.any(M)
        ld = []
    return N, E, dict(rank=rank, nullity=m-rank, pivots=pivots, free=free,
                     denominator=denominator, rref_numerator=N.tolist(),
                     positive_ldl_diagonal=ld)


def main():
    started = time.time()
    model = build(gram=True)
    X = c5_vector(model)
    A = model['A'].astype(np.int64)
    assert np.array_equal(model['A'].data, A.data)
    rhs = exact_int_array(model['rhs'])
    assert np.array_equal(A @ X, 160 * rhs)
    obj2 = exact_int_array(2 * model['obj'])
    assert int(obj2 @ X) == 400
    assert np.all((X >= 0) & (X <= 160))
    support = np.flatnonzero(X)
    variables_json = json.dumps([[n, list(c)] for n, c in model['variables']],
                                separators=(',', ':'))
    arrays = dict(X=X, denominator=np.array(160, dtype=np.int64), support=support,
                  support_numerator=X[support])
    blocks = []
    for j, (typ, m, K, D) in enumerate(model['blocks']):
        Ki = exact_int_array(K)
        Di = D.astype(np.int64)
        assert np.array_equal(D.data, Di.data)
        M = 160 * Ki + (Di @ X).reshape(m, m)
        assert np.array_equal(M, M.T)
        N, E, metadata = block_face(M)
        metadata.update(block=j, type=list(typ), size=m,
                        matrix_nonzeros=int(np.count_nonzero(M)),
                        active_coordinates=np.flatnonzero(np.any(M != 0, axis=0)).tolist())
        arrays[f'M_{j:03d}'] = M
        arrays[f'R_num_{j:03d}'] = N
        arrays[f'E_{j:03d}'] = E
        blocks.append(metadata)
        print(f"block {j:02d} size={m} rank={metadata['rank']} "
              f"active={len(metadata['active_coordinates'])} denom={metadata['denominator']}", flush=True)

    exact = {
        'schema': 'marked-root-order6-c5-face-v1',
        'interpretation': 'All ordered-root color-preserving maps to fully marked C5, including collisions; diagonal color 0.',
        'normalization': 'q_F=hom(F,C5)/(10*2^(|F|-2)); stored X=160*q.',
        'variables': len(X),
        'variable_order_sha256': hashlib.sha256(variables_json.encode()).hexdigest(),
        'q_denominator': 160,
        'q_support': [dict(index=int(i), order=model['variables'][i][0],
                           representative=list(model['variables'][i][1]), numerator=int(X[i]))
                      for i in support],
        'objective': '5/4',
        'kernel_convention': 'R=B^T=R_num/denominator; R[:,pivots]=I. v[free]=denominator*t and v[pivots]=-R_num[:,free]*t for any integer t. E maps t to v. For arbitrary common global L, v/L is an exact rational kernel vector.',
        'blocks': blocks,
    }
    np.savez_compressed(HERE / 'c5_face_data.npz', **arrays)
    (HERE / 'c5_face_data.json').write_text(json.dumps(exact, indent=2) + '\n')
    summary = dict(
        all_degree_equations_exact=True, all_57_blocks_exact_psd=True,
        all_kernel_relations_exact=True, all_kernel_bases_full_rank=True,
        all_q_in_unit_interval=True, objective='5/4', variables=len(X),
        degree_equations=len(rhs), support_size=len(support),
        support_by_order={str(k): sum(model['variables'][i][0] == k for i in support)
                          for k in (3, 4, 5, 6)},
        q_numerators=sorted(set(int(v) for v in X[support])),
        block_count=len(blocks), nonzero_blocks=[b['block'] for b in blocks if b['rank']],
        ranks=[b['rank'] for b in blocks], total_rank=sum(b['rank'] for b in blocks),
        total_nullity=sum(b['nullity'] for b in blocks),
        denominator_min=min(b['denominator'] for b in blocks),
        denominator_max=max(b['denominator'] for b in blocks),
        seconds=time.time()-started,
        sharp_upper_bound_proved=False,
    )
    (HERE / 'c5_face_verification.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary, indent=2), flush=True)


if __name__ == '__main__':
    main()
