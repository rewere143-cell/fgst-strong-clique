"""Independent validation using analytic/eigenvalue SDP optima, no other solver."""
from __future__ import annotations
import json
from pathlib import Path
import subprocess
import sys
import tempfile

import numpy as np
from scipy import sparse

import native_scs as scs

REPORT = []


def check(name, A, b, c, cone, target, target_x=None, **settings):
    result = scs.solve(A, b, c, cone, eps=settings.pop("eps", 1e-9), max_iters=100000, max_seconds=30, **settings)
    stats = scs.diagnostics(A, b, c, cone, result)
    assert result['info']['status_val'] == 1, (name, result['info'])
    assert abs(stats['primal_objective'] - target) < 2e-6, (name, stats, target)
    assert abs(stats['dual_objective'] - target) < 2e-6, (name, stats, target)
    assert stats['primal_residual_inf'] < 2e-6, (name, stats)
    assert stats['dual_residual_inf'] < 2e-6, (name, stats)
    assert abs(stats['complementarity']) < 2e-6, (name, stats)
    assert min(stats['psd_primal_min_eigenvalues'], default=0) >= -2e-6, (name, stats)
    assert min(stats['psd_dual_min_eigenvalues'], default=0) >= -2e-6, (name, stats)
    if target_x is not None:
        assert np.max(np.abs(result['x'] - target_x)) < 2e-6, (name, result['x'], target_x)
    REPORT.append({'test': name, 'expected_objective': float(target), 'info': result['info'], 'checks': stats})
    return result


def eigen_problem(M):
    A = sparse.csc_matrix(-scs.svec(np.eye(len(M))).reshape(-1, 1))
    return A, -scs.svec(M), np.array([1.]), {'s': [len(M)]}


def main():
    # The exact packed order is deliberately asserted independent of roundtrip.
    M = np.array([[11, 12, 13], [12, 22, 23], [13, 23, 33]], dtype=float)
    expected = np.array([11, 12*np.sqrt(2), 13*np.sqrt(2), 22, 23*np.sqrt(2), 33])
    np.testing.assert_array_equal(scs.svec(M), expected)
    np.testing.assert_allclose(scs.smat(expected), M, atol=1e-14, rtol=1e-14)
    N = np.array([[1., 2., 3.], [2., -2., 5.], [3., 5., 2.]])
    assert abs(scs.svec(M) @ scs.svec(N) - np.trace(M @ N)) < 1e-10

    # Nontrivial 3x3 cone: imposing only 2x2 principal PSD blocks would give 2, not 3.
    result = check('genuine_3x3_not_pairwise_SOC', *eigen_problem(np.ones((3, 3))), 3., [3.])
    np.testing.assert_allclose(scs.smat(result['y']), np.ones((3, 3))/3, atol=2e-6)

    # Distinct off-diagonal entries detect packed ordering and sqrt(2) mistakes.
    M = np.array([[2., 1., 3., -.5], [1., 0., .2, 2.], [3., .2, -1., .4], [-.5, 2., .4, 1.]])
    eigvals, eigvecs = np.linalg.eigh(M)
    problem = eigen_problem(M)
    result = check('asymmetric_4x4_order_and_scaling', *problem, eigvals[-1], [eigvals[-1]])
    np.testing.assert_allclose(scs.smat(result['y']), np.outer(eigvecs[:, -1], eigvecs[:, -1]), atol=2e-6)
    check('warm_start_same_problem', *problem, eigvals[-1], [eigvals[-1]],
          warm_start={k: result[k] for k in ['x', 'y', 's']})
    check('unaccelerated_scs_path', *problem, eigvals[-1], [eigvals[-1]], super_scs=False, eps=1e-8)
    check('without_normalization', *problem, eigvals[-1], [eigvals[-1]], normalize=False)

    # Coupled equalities and nonnegative cone plus two genuinely PSD blocks.
    # x=(t,u), u=2; tI_3-uJ_3 >=0 and tI_4-M >=0. Optimum t=6, u=2.
    # Equality multiplier must be -3 under A.T y+c=0.
    A = sparse.vstack([
        sparse.csc_matrix([[0., 1.]]), -sparse.eye(2, format='csc'),
        sparse.csc_matrix(np.column_stack([-scs.svec(np.eye(3)), scs.svec(np.ones((3,3)))])),
        sparse.csc_matrix(np.column_stack([-scs.svec(np.eye(4)), np.zeros(10)])),
    ], format='csc')
    b = np.r_[2., np.zeros(2+6), -scs.svec(M)]
    c = np.array([1., 0.])
    cone = {'f': 1, 'l': 2, 's': [3, 4]}
    result = check('equalities_nonnegative_multiple_PSD', A, b, c, cone, 6., [6., 2.])
    assert abs(result['y'][0] + 3.) < 2e-6, result['y'][0]
    assert result['s'][1:3].min() > 1.999999

    # Sparse affine conversion for caller's row-major block representation.
    D = sparse.csr_matrix(np.column_stack([np.eye(4).ravel(), -M.ravel()]))
    packed_A, packed_b = scs.affine_psd_rows(M, D)
    np.testing.assert_allclose(packed_A.toarray(), np.column_stack([-scs.svec(np.eye(4)), scs.svec(M)]))
    np.testing.assert_allclose(packed_b, scs.svec(M))
    try:
        scs.affine_psd_rows(M, sparse.csr_matrix(np.arange(16)[:, None]))
    except ValueError:
        pass
    else:
        raise AssertionError('Nonsymmetric affine coefficient accepted')

    # Repeated solves exercise cleanup and matrix copies; inputs must not mutate.
    before = (A.data.copy(), b.copy(), c.copy())
    rng = np.random.default_rng(20261103)
    for order in [3, 5, 8, 12]:
        M2 = rng.normal(size=(order, order)); M2 = (M2 + M2.T)/2
        expected = np.linalg.eigvalsh(M2)[-1]
        check(f'random_spectral_epigraph_{order}', *eigen_problem(M2), expected)
    for old, new in zip(before, [A.data, b, c]):
        np.testing.assert_array_equal(old, new)

    # Linear scalar edge case and strict dimension guards.
    check('simple_LP', sparse.csc_matrix([[-1.]]), [-2.], [1.], {'l': 1}, 2., [2.])
    for invalid in [{'s': [2]}, {'f': 1, 's': [3]}, {'s': [3], 'unknown': 1}]:
        try:
            scs.solve(*eigen_problem(np.eye(3))[:3], invalid)
        except ValueError:
            pass
        else:
            raise AssertionError(f'invalid cone accepted: {invalid}')

    # Prove subprocess CLI can read a sparse problem and write both numerical files.
    with tempfile.TemporaryDirectory() as temp:
        inp, out = Path(temp)/'problem.npz', Path(temp)/'solution.npz'
        np.savez_compressed(inp, A_data=A.data, A_indices=A.indices, A_indptr=A.indptr,
                            A_shape=A.shape, b=b, c=c, **cone)
        subprocess.run([sys.executable, str(Path(__file__).with_name('native_scs.py')),
                        str(inp), str(out), '--eps', '1e-9'], check=True, capture_output=True)
        r = np.load(out)
        np.testing.assert_allclose(r['x'], [6., 2.], atol=2e-6)
        assert json.loads(out.with_suffix('.json').read_text())['info']['status_val'] == 1

    # Status reporting on infeasibility and unboundedness, not false 'solved'.
    infeas = scs.solve(sparse.csc_matrix([[1.], [-1.]]), [0., -1.], [0.], {'l':2})
    assert infeas['info']['status_val'] in [-2, -7], infeas['info']
    unbdd = scs.solve(sparse.csc_matrix([[-1.]]), [0.], [-1.], {'l':1})
    assert unbdd['info']['status_val'] in [-1, -6], unbdd['info']
    REPORT.append({'test': 'infeasible_and_unbounded_status', 'infeasible': infeas['info'], 'unbounded': unbdd['info']})
    report = {'pass': True, 'tests': REPORT, 'description': 'Known analytic/eigenvalue optima; no second SDP solver used.'}
    output = Path(__file__).with_name('validation.json')
    output.write_text(json.dumps(scs.json_safe(report), indent=2, allow_nan=False) + '\n')
    print(json.dumps({'pass': True, 'tests': len(REPORT), 'report': str(output)}))


if __name__ == '__main__':
    main()
