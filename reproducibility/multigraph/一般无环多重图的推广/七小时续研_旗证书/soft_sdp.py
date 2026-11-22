"""Search with all Gram cones and one common PSD relaxation variable."""
from fractions import Fraction as F
import json

from half_anchor_flag import CACHE
from multigraph_refit_exact_dual import repair
from multigraph_weighted_maxdeg_exact import rounded_certificate, verify
from refit_scs_warm import scs_data


def soft_sdp(source, system, output, seconds, penalty, direct=False, refit=0):
    import numpy as np
    import scs
    from scipy.sparse import csr_matrix, hstack, vstack

    eq, iq, _, sizes, _, _, _, objective, _ = system
    base, cones = scs_data(system)
    end_linear = eq.shape[0]+iq.shape[0]+len(objective)
    blocks = []
    for size in sizes:
        rows, columns = np.tril_indices(size)
        order = np.lexsort((rows, columns))
        blocks.extend(-float(row == col) for row, col in zip(rows[order], columns[order]))
    assert len(blocks) == base["A"].shape[0] - end_linear
    linear = hstack([base["A"][:end_linear], csr_matrix((end_linear, 1))])
    nonnegative_t = csr_matrix(([-1.], ([0], [len(objective)])), shape=(1, len(objective)+1))
    semidefinite = hstack([base["A"][end_linear:], csr_matrix(np.array(blocks)[:, None])])
    a = vstack([linear, nonnegative_t, semidefinite], format="csc")
    b = np.insert(base["b"], end_linear, 0.)
    c = np.r_[base["c"], float(penalty)]
    cones["l"] += 1
    solver = scs.SCS(dict(A=a, b=b, c=c), cones,
                     linear_solver="qdldl" if direct else "cpu_indirect",
                     eps_abs=1e-7, eps_rel=1e-7, max_iters=30000,
                     time_limit_secs=seconds, verbose=True)
    solution = solver.solve()
    print(json.dumps(solution["info"], indent=2), flush=True)
    y = np.delete(solution["y"], end_linear)
    if not np.all(np.isfinite(y)):
        return
    path = output.with_suffix(".numerical.npz")
    np.savez_compressed(path, y=y)
    mode = "infeasible" if solution["info"]["status_val"] in (-2, -7) else "bound"
    certificate = rounded_certificate(CACHE, path, mode, source["settings"], system)
    certificate["projection_inputs"] = source["projection_inputs"]
    certificate["shadow_sha256"] = source["shadow_sha256"]
    result = verify(CACHE, certificate, system)
    certificate["replay_result"] = result
    output.write_text(json.dumps(certificate,separators=(",",":"))+"\n", encoding="utf-8")
    print(json.dumps(dict(raw=result)), flush=True)
    target = F(source["settings"]["mass_low"]) if mode == "bound" else F(0)
    if refit and F(result["rational_bound"]) >= target:
        try:
            refined = repair(CACHE, certificate, refit, system)
        except RuntimeError as error:
            print(json.dumps(dict(refit_error=str(error))), flush=True)
            return
        if F(refined["replay_result"]["rational_bound"]) < F(result["rational_bound"]):
            output.write_text(json.dumps(refined,separators=(",",":"))+"\n", encoding="utf-8")
        print(json.dumps(dict(refit=refined["replay_result"])), flush=True)
