"""Find exact exclusions by penalizing, rather than forbidding, provisional Gram cuts."""
from fractions import Fraction as F
import json
from math import sqrt
from pathlib import Path
import sys
from time import monotonic

from half_anchor_flag import CACHE
from multigraph_weighted_maxdeg_exact import verify


def soft_search(source, system, output, seconds, rounds, cut_limit, per_round,
                directions_path=None, penalty=1000, initial_directions=None, first_block=0,
                no_crossover=False, verbose=False):
    import numpy as np
    from scipy.optimize import linprog
    from scipy.sparse import csr_matrix, hstack, vstack

    eq, iq, grams, sizes, _, _, scale, objective, _ = system
    matrices = [g/scale for g in grams]
    dim = len(objective)
    aeq = hstack([eq/scale, csr_matrix((eq.shape[0], 1))], format="csr")
    old_iq = hstack([iq/scale, csr_matrix((iq.shape[0], 1))], format="csr")
    rhs = np.zeros(eq.shape[0])
    rhs[0] = 1
    c = np.r_[-objective/2, float(penalty)]
    ld = source["linear_denominator"]
    vd = source["vector_denominator"]
    target = F(source["settings"]["mass_low"])
    directions = []
    cut_rows = []

    def add(direction_rows):
        new_rows = []
        for block, x in direction_rows:
            normalized = np.asarray(x, dtype=np.float64)
            assert len(normalized) == sizes[block]
            norm = np.linalg.norm(normalized)
            if not norm:
                continue
            normalized = normalized/norm
            directions.append((block, normalized))
            cut = csr_matrix(-(matrices[block] @ np.outer(normalized, normalized).ravel()))
            new_rows.append(hstack([cut, csr_matrix([[-1.]])], format="csr"))
        cut_rows.extend(new_rows)
        return new_rows

    if initial_directions:
        add(json.loads(initial_directions.read_bytes()))

    repo = Path(__file__).resolve().parents[3]
    sys.path.insert(0, str(repo/"regeneration_20261105/source_full/extracted/strong_clique/flags/solver"))
    from native_highs import HighsError, IncrementalLP

    current_iq = vstack([old_iq, *cut_rows], format="csr")
    tolerances = (dict(primal_feasibility_tolerance=1e-6, dual_feasibility_tolerance=1e-6,
                       ipm_optimality_tolerance=1e-7) if no_crossover else {})
    native = IncrementalLP(c, aeq, rhs, current_iq, np.zeros(current_iq.shape[0]), threads=1,
                           verbose=verbose, **tolerances)

    def native_solve(limit):
        if not no_crossover:
            return native.solve(time_limit=limit)
        before = native.highs.getRunTime()
        native._set("time_limit", before+limit)
        native._set("solver", "ipm")
        native._set("presolve", "on")
        native._set("run_crossover", "off")
        status = native.highs.run()
        return native._result(status, "ipm", False, 0, before)
    began = monotonic()
    m = iq.shape[0]
    best = None
    for iteration in range(rounds+1):
        left = seconds-(monotonic()-began)
        if left <= 0:
            break
        try:
            fit = native_solve(min(per_round, left)) if native else None
        except HighsError:
            fit = None
        if fit and (fit["success"] or (no_crossover and fit["value_valid"] and fit["dual_valid"])):
            x, numeric = fit["x"], -fit["fun"]
            equality_duals = fit["equality_duals"]
            inequality_duals = fit["inequality_duals"]
        else:
            native = None
            current_iq = vstack([old_iq, *cut_rows], format="csr")
            fit = linprog(c, A_eq=aeq, b_eq=rhs, A_ub=current_iq,
                          b_ub=np.zeros(current_iq.shape[0]), bounds=(0, None),
                          method="highs-ipm", options={"time_limit": min(per_round, left)})
            if not fit.success:
                print(json.dumps(dict(iteration=iteration, status=fit.message)), flush=True)
                break
            x, numeric = fit.x, -fit.fun
            equality_duals = fit.eqlin.marginals
            inequality_duals = fit.ineqlin.marginals

        candidate = dict(source, mode="bound")
        candidate["equalities"] = [round(-v*ld) for v in equality_duals]
        dual = -inequality_duals
        candidate["inequalities"] = [max(0, round(v*ld)) for v in dual[:m]]
        candidate["gram_squared_vectors"] = [[] for _ in sizes]
        for weight, (block, vector) in zip(dual[m:], directions):
            if weight > 0:
                scaled = [round(float(y)*sqrt(weight)*vd) for y in vector]
                if any(scaled):
                    candidate["gram_squared_vectors"][block].append(scaled)
        result = verify(CACHE, candidate, system)
        value = F(result["rational_bound"])
        print(json.dumps(dict(iteration=iteration, score=float(numeric), softness=float(x[-1]),
                              cuts=len(directions), exact=result)), flush=True)
        if best is None or value < best:
            best = value
            candidate["replay_result"] = result
            output.write_text(json.dumps(candidate,separators=(",",":"))+"\n", encoding="utf-8")
        if value < target:
            break

        violations = []
        for block in range(first_block, len(sizes)):
            g = (matrices[block].T @ x[:dim]).reshape(sizes[block], sizes[block])
            eigenvalues, basis = np.linalg.eigh((g+g.T)/2)
            for k in np.flatnonzero(eigenvalues < -x[-1]-1e-9)[:3]:
                violations.append((eigenvalues[k], block, basis[:, k]))
        if not violations:
            break
        violations.sort(key=lambda item: item[0])
        new_constraints = add((block, x) for _, block, x in violations[:cut_limit])
        if native and new_constraints:
            native.add_inequalities(vstack(new_constraints, format="csr"), np.zeros(len(new_constraints)))
        if directions_path:
            contents = [(int(block), vector.tolist()) for block, vector in directions]
            directions_path.write_text(json.dumps(contents,separators=(",",":"))+"\n", encoding="utf-8")
