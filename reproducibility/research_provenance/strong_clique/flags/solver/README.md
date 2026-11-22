# Native sparse SDP solver, using installed SuperSCS

This directory provides `native_scs.py`, a reusable NumPy/SciPy interface to the
**already installed** SuperSCS in CasADi 3.7.2. The solver identifies itself as
SuperSCS/SCS 1.3.3. No software was installed or downloaded. The only compiled
code is the small local ABI adapter `superscs_bridge.cpp`.

## Mathematical convention

The interface solves

```
minimize       c.T @ x
subject to     A @ x + s = b
               s in K.
```

`x` is a free vector. Its nonnegativity is **not implicit**. Add `A=-I, b=0`
rows in the nonnegative cone to enforce `x >= 0`.

The returned dual multiplier `y` uses

```
maximize       -b.T @ y
subject to     A.T @ y + c = 0
               y in dual(K).
```

The rows of `A` and `b`, and corresponding entries of `s` and `y`, must be in
this exact cone order:

1. `cone['f']` zero-cone rows, so `A_eq @ x = b_eq`. `z` is an alias for `f`.
2. `cone['l']` nonnegative rows, so `A_ineq @ x <= b_ineq`.
3. The second-order cones in `cone.get('q', [])`, if used.
4. The positive-semidefinite blocks in `cone['s']`.

`cone['s']` contains **matrix orders**, not packed vector lengths. A block of
order `r` occupies `r*(r+1)//2` rows. Multiple blocks are supported directly.
All index arrays in the C ABI are 64-bit; numeric arrays are double precision.
The wrapper converts SciPy CSC indices as needed, sums duplicates, sorts row
indices, rejects non-finite inputs and dimension mistakes, and copies inputs.

### Exact PSD vectorization convention

Use `svec(X)`: lower triangle, **column-major**, with off-diagonals multiplied
by `sqrt(2)`. For a 3-by-3 matrix:

```
svec(X) = [X00, sqrt(2)*X10, sqrt(2)*X20, X11, sqrt(2)*X21, X22].
```

The inverse is `smat(v)`. This scaling gives
`dot(svec(X), svec(Y)) = trace(X @ Y)` for symmetric matrices, and preserves the
self-duality of the PSD cone. The returned dual PSD segment is unpacked by
**the same** `smat` function.

To impose `M(x) = K + reshape(D @ x, (r,r)) >= 0`, with `D` using NumPy's
ordinary **row-major** flattening:

```
A_psd, b_psd = affine_psd_rows(K, D)
```

This takes flattened rows `i*r+j`, ordered by `j=0..r-1, i=j..r-1`, scales
off-diagonals by `sqrt(2)`, negates the coefficients, and sets `b_psd=svec(K)`.
It checks the coefficient matrices' symmetry without densifying `D`.
For a nonsymmetric representation, symmetrize the affine matrices before
packing, rather than silently throwing away one triangle.

## Python API

```python
import sys
sys.path.insert(0, 'strong_clique/flags/solver')
import native_scs
from scipy import sparse
import numpy as np

# min t, t*I - J is PSD. True optimum is t=3.
A = sparse.csc_matrix(-native_scs.svec(np.eye(3))[:, None])
b = -native_scs.svec(np.ones((3,3)))
c = np.array([1.0])
cone = {'s': [3]}
result = native_scs.solve(A, b, c, cone, eps=1e-8)
print(result['x'])             # approximately [3.0]
print(result['info'])
print(native_scs.smat(result['y']))  # approximately J/3
print(native_scs.diagnostics(A, b, c, cone, result))
```

Returned fields:

- `x`: primal variables, length `n`.
- `y`: dual row multipliers, length `m`.
- `s`: primal conic slack, length `m`.
- `info`: status string/code, primal and dual objectives, solver residuals,
  gap, iterations, timing, CG iteration count, and native solver version.

Call `diagnostics(A,b,c,cone,result)` for **independently recomputed** infinity
norm primal/dual equation residuals, objectives, gap, complementarity,
nonnegative cone minima, and each primal/dual PSD block's minimum eigenvalue.
These checks are numerical, not exact proof certificates.

Supported keyword settings (defaults):

```
eps=1e-7                 max_iters=100000       max_seconds=300
verbose=False           super_scs=True        normalize=True
scale=1.0               rho_x=1e-3            memory=10
alpha=1.5               cg_rate=2.0           warm_start=None
```

This installed solver uses **sparse-indirect conjugate gradients** for its
linear system, not a direct factorization. `super_scs=False` selects its
unaccelerated SCS path. `memory` controls Anderson acceleration and is capped
at `m+n` for tiny problems. Warm start with

```python
warm_start={key: previous_result[key] for key in ['x','y','s']}
```

for a problem with the same dimensions and cone layout. Solver settings are
per call; there is no persistent factorization. Calls are serialized by a
Python lock because native SuperSCS uses process-level interrupt handling.
For larger independent jobs, use separate processes.

Start compute jobs with `OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1` as a sensible
baseline. CasADi ships a separate OpenBLAS library; uncontrolled threading can
make many small PSD eigensolves slower. Benchmark additional threads if some
PSD blocks are large.

### Status codes and interpretation

- `1`: Solved to the solver's requested numerical tolerance.
- `2`: Solved/Inaccurate, including an iteration/time limit with a candidate.
- `-2`, `-7`: Infeasible / Infeasible-Inaccurate.
- `-1`, `-6`: Unbounded / Unbounded-Inaccurate.
- `-3`, `-4`, `-5`: Indeterminate / Failure / Interrupted.

An accurate-looking objective alone is not proof of feasibility or a valid
bound. Inspect all residuals and eigenvalues, and perform rational/exact
certificate verification for mathematical claims. In infeasible/unbounded
cases some primal/dual arrays and diagnostics are naturally NaN.

## Sparse file input and output

The command-line interface reads an NPZ with:

```
A_data, A_indices, A_indptr, A_shape  # SciPy CSC arrays and (m,n)
b, c                                # dense numeric vectors
f, l, q, s                          # cone dimensions; omitted means empty
```

Example invocation:

```
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python strong_clique/flags/solver/native_scs.py problem.npz solution.npz --eps 1e-7 --max-seconds 1800
```

It writes `solution.npz` containing `x,y,s`, plus `solution.json` containing
solver information and independent numerical checks. JSON uses `null` for
non-finite diagnostic values. `--plain-scs` disables SuperSCS acceleration.

## Build and provenance

The bridge autocompiles on first use if absent or older than its source. To
rebuild explicitly, run `python -c "import native_scs; native_scs.build()"`
from this directory. It requires the existing `g++`, CasADi headers/shared
libraries, NumPy and SciPy. `CASADI_DIR` can override the located installed
CasADi directory and `CXX` can override the C++ compiler. A bridge build uses
an atomic file replacement so it never overwrites an already mapped library.

The tested CasADi directory is:

```
/opt/codex/runtimes/codex-primary-runtime/dependencies/python/lib/python3.12/site-packages/casadi
```

The adapter links `libcasadi_conic_superscs.so`, which resolves the installed
CasADi and OpenBLAS dependencies through its existing rpath. ABI definitions
come directly from installed `include/superscs/scs.h`, `glbopts.h`,
`cones.h`, `constants.h`, and `linsys/amatrix.h`. In this distribution,
`scs_int` is a 64-bit integer and `scs_float` is double; the bridge has compile
assertions for both.

## Validation

Run:

```
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python strong_clique/flags/solver/test_native_scs.py
```

The independently known objectives and dual matrices test:

- A genuine 3-by-3 PSD constraint: `min t, tI-J >= 0` gives `t=3`; merely
  enforcing 2-by-2 principal PSD constraints would instead give `t=2`.
- A 4-by-4 matrix with all distinct off-diagonal values, with optimum equal
  to its independently computed largest eigenvalue. Its returned dual is the
  top eigenvector's rank-one projector. This detects order/scaling errors.
- Equality and nonnegative rows together with two PSD blocks of orders 3,4.
  The optimum is `(t,u)=(6,2)` and the equality multiplier is `-3`.
- Warm starts, no normalization, unaccelerated SCS, random spectral epigraphs
  of orders 3,5,8,12, a scalar LP, infeasible/unbounded statuses, invalid-input
  guards, sparse affine packing, and NPZ command-line roundtripping.

`validation.json` records all results. The current suite passes. At very tight
`eps=1e-9`, the unaccelerated path can stall around a residual of a few `1e-9`;
its test uses `eps=1e-8`. All other solved checks use `eps=1e-9`, with independent
objective/feasibility assertions at `2e-6`. No second SDP solver is needed for
these checks, because the true objectives are analytic or ordinary eigenvalues.
