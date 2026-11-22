"""Small consumers of c5_face_data.json. Integer reconstruction is exact."""
from __future__ import annotations

import json
from pathlib import Path
import numpy as np

HERE = Path(__file__).resolve().parent


def load_face():
    return json.loads((HERE / 'c5_face_data.json').read_text())


def constraint_numerator(block):
    return np.asarray(block['rref_numerator'], dtype=np.int64).reshape(block['rank'], block['size'])


def project_to_kernel(vector, block):
    """Orthogonally project one floating vector to the exact rational kernel."""
    vector = np.asarray(vector, dtype=float)
    assert vector.shape == (block['size'],)
    if not block['rank']:
        return vector.copy()
    N = constraint_numerator(block).astype(float)
    return vector - N.T @ np.linalg.solve(N @ N.T, N @ vector)


def reconstruct_integer_factor(free_numerator, block):
    """Construct a Python-integer numerator; free entries must be multiples D.

    This works for arbitrary integer magnitudes and cannot overflow int64.
    """
    denominator = block['denominator']
    free = block['free']
    pivots = block['pivots']
    assert all(isinstance(v, (int, np.integer)) for v in free_numerator)
    values = [int(v) for v in free_numerator]
    assert len(values) == len(free)
    assert all(v % denominator == 0 for v in values)
    t = [v // denominator for v in values]
    result = [0] * block['size']
    for i, v in zip(free, values):
        result[i] = v
    for i, row in zip(pivots, block['rref_numerator']):
        result[i] = -sum(row[j] * v for j, v in zip(free, t))
    assert all(sum(c * v for c, v in zip(row, result)) == 0
               for row in block['rref_numerator'])
    return result


def round_kernel_factor(vector, block, scale, project=True):
    """Return integer a such that a/scale approximates vector and M*a=0.

    scale is any common positive integer across all blocks. Per-block D only
    coarsens free-coordinate rounding; it does not enter the denominator of
    a/scale. Thus the SOS denominator is scale**2 without a cross-block LCM.
    Floating rounding is for approximation only; all kernel identities are
    re-established with Python integer arithmetic by reconstruction.
    """
    assert isinstance(scale, int) and scale > 0
    target = project_to_kernel(vector, block) if project else np.asarray(vector, dtype=float)
    assert target.shape == (block['size'],) and np.all(np.isfinite(target))
    D = block['denominator']
    free = [D * round(float(target[i]) * scale / D) for i in block['free']]
    return reconstruct_integer_factor(free, block)


def verify_integer_factor(numerator, block, matrix=None):
    """Validate the rational constraints and optionally every original M row."""
    assert len(numerator) == block['size']
    assert all(isinstance(v, (int, np.integer)) for v in numerator)
    v = [int(x) for x in numerator]
    assert all(sum(int(c) * x for c, x in zip(row, v)) == 0
               for row in block['rref_numerator'])
    if matrix is not None:
        assert all(sum(int(c) * x for c, x in zip(row, v)) == 0 for row in matrix)
    return True
