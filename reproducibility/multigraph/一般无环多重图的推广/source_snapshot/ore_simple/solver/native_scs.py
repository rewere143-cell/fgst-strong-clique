"""Sparse conic SDP wrapper around the SuperSCS already bundled with CasADi.

Solve min c.T @ x subject to A @ x + s = b, s in K.
K row order: zero cone, nonnegative cone, SOCs, PSD cones.
A PSD block is lower-triangular, column-major, with off-diagonals times sqrt(2).
No solver download or installation is performed. See README.md.
"""
from __future__ import annotations

import ctypes as ct
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import threading

import numpy as np
from scipy import sparse

_HERE = Path(__file__).resolve().parent
_LIB = None
_LOCK = threading.Lock()  # SuperSCS installs process-wide signal handlers.
_F64 = np.ctypeslib.ndpointer(dtype=np.float64, ndim=1, flags="C_CONTIGUOUS")
_I64 = np.ctypeslib.ndpointer(dtype=np.int64, ndim=1, flags="C_CONTIGUOUS")
_INT_FIELDS = ("iter", "status_val", "cg_total_iters")
_FLOAT_FIELDS = (
    "pobj", "dobj", "res_pri", "res_dual", "res_infeas", "res_unbdd",
    "rel_gap", "setup_time_ms", "solve_time_ms", "linsys_time_ms", "allocated_memory",
)


def build() -> Path:
    """Compile only our tiny bridge against installed headers and shared library."""
    override = os.environ.get("CASADI_DIR")
    spec = importlib.util.find_spec("casadi")
    root = Path(override) if override else Path(spec.origin).parent if spec else None
    if root is None or not (root / "include/superscs/scs.h").is_file():
        raise RuntimeError("Installed CasADi SuperSCS headers not found; set CASADI_DIR.")
    output = _HERE / "libsuperscs_bridge.so"
    cmd = [os.environ.get("CXX", "g++"), "-std=c++11", "-O2", "-fPIC", "-shared",
           str(_HERE / "superscs_bridge.cpp"), f"-I{root / 'include'}", f"-L{root}",
           "-lcasadi_conic_superscs", f"-Wl,-rpath,{root}", "-o", str(output.with_suffix(f".tmp.{os.getpid()}.so"))]
    temporary = output.with_suffix(f".tmp.{os.getpid()}.so")
    try:
        subprocess.run(cmd, check=True)
        temporary.replace(output)  # Never overwrite an already mapped shared library.
    finally:
        temporary.unlink(missing_ok=True)
    return output


def _library():
    global _LIB
    if _LIB is None:
        path = _HERE / "libsuperscs_bridge.so"
        if not path.exists() or path.stat().st_mtime < (_HERE / "superscs_bridge.cpp").stat().st_mtime:
            build()
        _LIB = ct.CDLL(str(path))
        _LIB.native_scs_version.restype = ct.c_char_p
        _LIB.native_scs_solve.argtypes = [
            ct.c_int64, ct.c_int64, _F64, _I64, _I64, _F64, _F64,
            ct.c_int64, ct.c_int64, ct.c_int64, _I64, ct.c_int64, _I64,
            ct.c_double, ct.c_int64, ct.c_double, ct.c_int64,
            ct.c_int64, ct.c_int64, ct.c_double, ct.c_double, ct.c_int64, ct.c_int64,
            ct.c_double, ct.c_double, _F64, _F64, _F64, _F64, _I64, ct.c_void_p,
        ]
        _LIB.native_scs_solve.restype = ct.c_int64
    return _LIB


def svec(matrix):
    """Frobenius-isometric lower-column vectorization of a symmetric matrix."""
    matrix = np.asarray(matrix, dtype=float)
    if matrix.ndim != 2 or matrix.shape[0] != matrix.shape[1]:
        raise ValueError("svec expects a square matrix")
    if not np.allclose(matrix, matrix.T, atol=1e-12, rtol=1e-12):
        raise ValueError("svec expects a symmetric matrix")
    n = len(matrix)
    return np.array([matrix[i, j] * (1.0 if i == j else np.sqrt(2.0))
                     for j in range(n) for i in range(j, n)], dtype=float)


def smat(vector, order=None):
    """Inverse of svec. Off-diagonal vector entries are divided by sqrt(2)."""
    vector = np.asarray(vector, dtype=float).reshape(-1)
    if order is None:
        order = int((np.sqrt(1 + 8 * len(vector)) - 1) / 2)
    if order < 0 or order * (order + 1) // 2 != len(vector):
        raise ValueError("Packed PSD vector length is not triangular")
    result = np.zeros((order, order), dtype=float)
    k = 0
    for j in range(order):
        for i in range(j, order):
            result[i, j] = result[j, i] = vector[k] / (1.0 if i == j else np.sqrt(2.0))
            k += 1
    return result



def affine_psd_rows(K, D, *, check_symmetry=True):
    """Return A_block,b_block for K + reshape(D @ x, (r,r)) >= 0.

    D uses ordinary C/row-major flattening and has r*r rows. K is r by r.
    Select lower entries in column order, multiply off-diagonals by sqrt(2),
    and negate coefficients to match A @ x+s=b. No dense D is constructed.
    """
    K = np.asarray(K, dtype=float)
    if K.ndim != 2 or K.shape[0] != K.shape[1]:
        raise ValueError("K must be a square matrix")
    order = len(K)
    D = sparse.csr_matrix(D, dtype=np.float64, copy=True)
    if D.shape[0] != order * order:
        raise ValueError("D must have order squared rows (row-major flattening)")
    if check_symmetry:
        transpose_rows = np.arange(order*order).reshape(order, order).T.ravel()
        diff = D - D[transpose_rows]
        if diff.nnz and np.max(np.abs(diff.data)) > 1e-12:
            raise ValueError("Affine coefficient matrices are not symmetric")
    rows = np.array([i*order+j for j in range(order) for i in range(j, order)])
    scales = np.array([1.0 if i == j else np.sqrt(2.0)
                       for j in range(order) for i in range(j, order)])
    A = D[rows].multiply(-scales[:, None]).tocsc()
    return A, svec(K)


def _nonnegative_int(value, name):
    result = int(value)
    if result != value or result < 0:
        raise ValueError(f"{name} must be a nonnegative integer")
    return result


def solve(A, b, c, cone, *, eps=1e-7, max_iters=100000, max_seconds=300,
          verbose=False, super_scs=True, normalize=True, scale=1.0,
          rho_x=1e-3, memory=10, warm_start=None, alpha=1.5, cg_rate=2.0):
    """Return x, y, s, info for min c'x, A x+s=b, s in the indicated cone.

    cone={'f': equality_count, 'l': nonnegative_count, 'q': SOC_orders,
          's': PSD_matrix_orders}. 'z' is accepted as an alias for 'f'.
    Dual convention: maximize -b'y, A'y+c=0, y in dual(K).
    All inputs are copied, and primal x is free unless rows explicitly constrain it.
    An optional warm_start dict contains x (n), y (m), and/or s (m).
    """
    unknown = set(cone) - {"f", "z", "l", "q", "s"}
    if unknown:
        raise ValueError(f"Unsupported cone keys: {sorted(unknown)}")
    if "z" in cone and "f" in cone and cone["z"] != cone["f"]:
        raise ValueError("Conflicting f and z zero-cone dimensions")
    f = _nonnegative_int(cone.get("f", cone.get("z", 0)), "f")
    l = _nonnegative_int(cone.get("l", 0), "l")
    q = np.array([_nonnegative_int(i, "q entry") for i in cone.get("q", [])], dtype=np.int64)
    s = np.array([_nonnegative_int(i, "s entry") for i in cone.get("s", [])], dtype=np.int64)
    if any(q < 2) or any(s < 1):
        raise ValueError("SOC orders must be >=2 and PSD orders >=1")
    A = sparse.csc_matrix(A, dtype=np.float64, copy=True)
    A.sum_duplicates()
    A.sort_indices()
    A.eliminate_zeros()
    m, n = A.shape
    if m <= 0 or n <= 0:
        raise ValueError("A must have positive row and column dimensions")
    expected_m = f + l + sum(int(i) for i in q) + sum(int(i) * (int(i) + 1) // 2 for i in s)
    if expected_m != m:
        raise ValueError(f"Cone row count {expected_m} does not match A rows {m}")
    b = np.array(b, dtype=np.float64, copy=True).reshape(-1)
    c = np.array(c, dtype=np.float64, copy=True).reshape(-1)
    if len(b) != m or len(c) != n:
        raise ValueError("b/c dimensions do not match A")
    if not all(np.all(np.isfinite(v)) for v in [A.data, b, c]):
        raise ValueError("A, b, c must be finite")
    if not all(np.isfinite(v) and v > 0 for v in [eps, max_seconds, scale, rho_x]):
        raise ValueError("eps, max_seconds, scale, rho_x must be positive finite numbers")
    if not np.isfinite(alpha) or not 0 < alpha < 2 or not np.isfinite(cg_rate) or cg_rate <= 0:
        raise ValueError("alpha must be in (0,2); cg_rate must be positive finite")
    max_iters = _nonnegative_int(max_iters, "max_iters")
    memory = _nonnegative_int(memory, "memory")
    if max_iters < 1 or memory < 2:
        raise ValueError("max_iters must be >=1 and memory >=2")
    data = np.ascontiguousarray(A.data, dtype=np.float64)
    indices = np.ascontiguousarray(A.indices, dtype=np.int64)
    indptr = np.ascontiguousarray(A.indptr, dtype=np.int64)
    memory = min(memory, m + n)  # Anderson history must fit its ambient vector space.
    arrays = {key: np.zeros(dim, dtype=np.float64) for key, dim in [("x", n), ("y", m), ("s", m)]}
    if warm_start is not None:
        for key, value in warm_start.items():
            if key not in arrays:
                raise ValueError(f"Unknown warm-start field {key}")
            value = np.asarray(value, dtype=np.float64).reshape(-1)
            if value.shape != arrays[key].shape or not np.all(np.isfinite(value)):
                raise ValueError(f"Invalid warm-start {key}")
            arrays[key][:] = value
    stats = np.full(len(_FLOAT_FIELDS), np.nan)
    ints = np.zeros(len(_INT_FIELDS), dtype=np.int64)
    status = ct.create_string_buffer(32)
    with _LOCK:
        lib = _library()
        result = lib.native_scs_solve(
            m, n, data, indices, indptr, b, c, f, l, len(q), q, len(s), s,
            eps, max_iters, max_seconds, int(verbose), int(super_scs), int(normalize),
            scale, rho_x, memory, int(warm_start is not None), alpha, cg_rate,
            arrays["x"], arrays["y"], arrays["s"], stats, ints, status)
    info = {key: float(value) for key, value in zip(_FLOAT_FIELDS, stats)}
    info.update({key: int(value) for key, value in zip(_INT_FIELDS, ints)})
    info.update(status=status.value.decode(errors="replace"), return_code=int(result),
                solver="CasADi-bundled SuperSCS", version=lib.native_scs_version().decode())
    if result == -99:
        raise MemoryError("SuperSCS could not allocate its info structure")
    arrays["info"] = info
    return arrays


def diagnostics(A, b, c, cone, result):
    """Independent numerical KKT checks. These are not exact certificates."""
    x, y, slack = (np.asarray(result[k]) for k in ("x", "y", "s"))
    A = sparse.csc_matrix(A)
    b, c = np.asarray(b), np.asarray(c)
    f = int(cone.get("f", cone.get("z", 0)))
    l = int(cone.get("l", 0))
    offset = f + l
    out = {
        "primal_residual_inf": float(np.linalg.norm(A @ x + slack - b, np.inf)),
        "dual_residual_inf": float(np.linalg.norm(A.T @ y + c, np.inf)),
        "primal_objective": float(c @ x),
        "dual_objective": float(-b @ y),
        "absolute_gap": float(abs(c @ x + b @ y)),
        "complementarity": float(slack @ y),
        "zero_slack_max_abs": float(np.max(np.abs(slack[:f]))) if f else 0.0,
        "nonnegative_slack_min": float(np.min(slack[f:f+l])) if l else None,
        "nonnegative_dual_min": float(np.min(y[f:f+l])) if l else None,
        "soc_primal_margins": [], "soc_dual_margins": [],
        "psd_primal_min_eigenvalues": [], "psd_dual_min_eigenvalues": [],
    }
    for size in cone.get("q", []):
        for vector, key in [(slack, "soc_primal_margins"), (y, "soc_dual_margins")]:
            v = vector[offset:offset+size]
            out[key].append(float(v[0] - np.linalg.norm(v[1:])))
        offset += size
    for order in cone.get("s", []):
        size = order * (order+1) // 2
        for vector, key in [(slack, "psd_primal_min_eigenvalues"), (y, "psd_dual_min_eigenvalues")]:
            block = vector[offset:offset+size]
            out[key].append(float(np.linalg.eigvalsh(smat(block, order))[0]) if np.all(np.isfinite(block)) else None)
        offset += size
    return out


def json_safe(value):
    """Replace non-finite diagnostic floats with null for standards-compliant JSON."""
    if isinstance(value, dict):
        return {key: json_safe(item) for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return [json_safe(item) for item in value]
    if isinstance(value, (float, np.floating)) and not np.isfinite(value):
        return None
    return value


def main():
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", help="NPZ with A_data, A_indices, A_indptr, A_shape, b, c, f/l/q/s")
    parser.add_argument("output", help="Output NPZ; a matching .json contains solver info and checks")
    parser.add_argument("--eps", type=float, default=1e-7)
    parser.add_argument("--max-iters", type=int, default=100000)
    parser.add_argument("--max-seconds", type=float, default=300)
    parser.add_argument("--verbose", action="store_true")
    parser.add_argument("--plain-scs", action="store_true")
    args = parser.parse_args()
    with np.load(args.input, allow_pickle=False) as p:
        A = sparse.csc_matrix((p["A_data"], p["A_indices"], p["A_indptr"]), shape=tuple(p["A_shape"]))
        b, c = p["b"], p["c"]
        cone = {key: p[key].tolist() for key in ["f", "z", "l", "q", "s"] if key in p}
    result = solve(A, b, c, cone, eps=args.eps, max_iters=args.max_iters,
                   max_seconds=args.max_seconds, verbose=args.verbose, super_scs=not args.plain_scs)
    np.savez_compressed(args.output, x=result["x"], y=result["y"], s=result["s"])
    metadata = json_safe({"info": result["info"], "diagnostics": diagnostics(A, b, c, cone, result)})
    Path(args.output).with_suffix(".json").write_text(json.dumps(metadata, indent=2) + "\n")
    print(json.dumps(metadata, indent=2))


if __name__ == "__main__":
    main()
