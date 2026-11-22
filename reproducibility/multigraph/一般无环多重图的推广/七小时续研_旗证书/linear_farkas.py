"""Recover a normalized certificate when the linear flag rows already contradict."""
from fractions import Fraction as F
import json

from half_anchor_flag import CACHE
from multigraph_weighted_maxdeg_exact import verify


def fit_linear_farkas(source, system, output, seconds, verbose):
    import numpy as np
    from scipy.optimize import linprog
    from scipy.sparse import csr_matrix, hstack, vstack

    eq, iq, _, sizes, _, _, scale, objective, _ = system
    shape = len(objective)
    normalization = hstack([eq[:1]/scale, csr_matrix((1, 1))], format="csr")
    rem_eq = eq[1:]/scale
    ine = iq/scale
    rows = vstack([rem_eq, -rem_eq, ine], format="csr")
    magnitude = np.maximum(1., np.asarray(abs(rows).max(axis=1).toarray()).ravel())
    scaled = rows.multiply(1/magnitude[:, None])
    penalties = csr_matrix((-np.ones(rows.shape[0]))[:, None])
    lhs = hstack([scaled, penalties], format="csr")
    c = np.r_[np.zeros(shape), 1.]
    result = linprog(c, A_ub=lhs, b_ub=np.zeros(rows.shape[0]), A_eq=normalization,
                     b_eq=np.ones(1), bounds=(0, None), method="highs-ipm",
                     options=dict(time_limit=seconds, disp=verbose,
                                  primal_feasibility_tolerance=1e-8,
                                  dual_feasibility_tolerance=1e-8))
    print(json.dumps(dict(status=result.message, linear_softness=result.fun)), flush=True)
    if not result.success or result.fun <= 0:
        return
    d = (-result.ineqlin.marginals/magnitude)/float(result.fun)
    count = rem_eq.shape[0]
    l = source["linear_denominator"]
    candidate = dict(source, mode="infeasible", gram_squared_vectors=[[] for _ in sizes])
    candidate["equalities"] = [round(-float(result.eqlin.marginals[0])/result.fun*l)]
    candidate["equalities"].extend(round(float(x)*l) for x in d[:count]-d[count:2*count])
    candidate["inequalities"] = [max(0, round(float(x)*l)) for x in d[2*count:]]
    exact = verify(CACHE, candidate, system)
    print(json.dumps(dict(exact=exact)), flush=True)
    if F(exact["rational_bound"]) < 0:
        candidate["replay_result"] = exact
        output.write_text(json.dumps(candidate,separators=(",",":"))+"\n", encoding="utf-8")
