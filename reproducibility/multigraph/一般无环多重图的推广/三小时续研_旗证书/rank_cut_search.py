"""Search for smaller exact bounds by pricing violated Gram directions."""
import argparse
from fractions import Fraction as F
import json
from math import sqrt
from pathlib import Path
import sys
from time import monotonic
from types import SimpleNamespace


HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))

from half_anchor_flag import CACHE, strengthened_system, verify_projection_inputs
from half_anchor_shadow import SHADOW, build_system
from multigraph_six_shadow_search import shadow_hashes
from multigraph_weighted_maxdeg_exact import verify


def infeasibility_candidate(original, A, D, cuts, cut_rows, sizes, denom, remaining):
    """Fit a normalized linear Farkas certificate after PSD directions are fixed."""
    import numpy as np
    from scipy.optimize import linprog
    from scipy.sparse import csr_matrix, hstack, vstack

    inequalities = vstack([D, *cut_rows], format="csr")
    count_eq = A.shape[0]
    dim = count_eq + inequalities.shape[0]
    unit = csr_matrix(([1.0], ([0], [0])), shape=(1, dim))
    fit = linprog(np.r_[np.zeros(count_eq), np.ones(inequalities.shape[0])],
                  A_ub=-hstack([A.T, inequalities.T], format="csr"), b_ub=np.zeros(A.shape[1]),
                  A_eq=unit, b_eq=[-1], bounds=[(None,None)]*count_eq+[(0,None)]*inequalities.shape[0],
                  method="highs-ipm", options={"time_limit": min(remaining, 180)})
    if not fit.success:
        print(json.dumps({"linear_dual_error": fit.message}), flush=True)
        return None
    candidate = dict(original, mode="infeasible")
    candidate["equalities"] = [round(float(v)*denom) for v in fit.x[:count_eq]]
    candidate["inequalities"] = [max(0,round(float(v)*denom))
                                  for v in fit.x[count_eq:count_eq+D.shape[0]]]
    vd = original["vector_denominator"]
    candidate["gram_squared_vectors"] = [[] for _ in sizes]
    for val, (block, vector) in zip(fit.x[count_eq+D.shape[0]:], cuts):
        if val > 0:
            factor = [round(float(x)*sqrt(val)*vd) for x in vector]
            if any(factor):
                candidate["gram_squared_vectors"][block].append(factor)
    return candidate


def triangle_density_candidate(original, system, cut_indices, cut_rows, remaining):
    """Allow red triangles again and certify a lower bound on their flag mass."""
    import numpy as np
    from scipy.optimize import linprog
    from scipy.sparse import vstack

    from k5_turan_rows import contains_red_clique

    eq, iq, grams, sizes, data, tags, scale, _, roots = system
    tri = contains_red_clique(data, 3)
    zero_lines = [
        i for i in range(iq.shape[0])
        if iq[i].nnz == int(tri.sum()) and
        np.array_equal(iq[i].toarray().ravel(), tri * scale)
    ]
    assert len(zero_lines) == 1, zero_lines
    keep = np.ones(iq.shape[0], dtype=bool)
    keep[zero_lines[0]] = False
    sub_iq = iq[keep]
    constraints = vstack([sub_iq / scale, *cut_rows], format="csr")
    rhs = np.zeros(eq.shape[0])
    rhs[0] = 1
    fit = linprog(tri.astype(np.float64), A_ub=constraints,
                  b_ub=np.zeros(constraints.shape[0]), A_eq=eq/scale, b_eq=rhs,
                  bounds=(0, None), method="highs-ipm",
                  options={"time_limit": min(remaining, 650)})
    if not fit.success:
        print(json.dumps({"triangle_density_error": fit.message}), flush=True)
        return None
    settings = dict(original["settings"], triangle_density_objective=True)
    candidate = dict(original, mode="bound", settings=settings)
    ld = original["linear_denominator"]
    vd = original["vector_denominator"]
    candidate["equalities"] = [round(-float(v)*ld) for v in fit.eqlin.marginals]
    dual = -fit.ineqlin.marginals
    candidate["inequalities"] = [max(0,round(float(v)*ld)) for v in dual[:sub_iq.shape[0]]]
    candidate["gram_squared_vectors"] = [[] for _ in sizes]
    for val, (block, vector) in zip(dual[sub_iq.shape[0]:], cut_indices):
        if val > 0:
            factor = [round(float(x)*sqrt(val)*vd) for x in vector]
            if any(factor):
                candidate["gram_squared_vectors"][block].append(factor)
    record = verify(CACHE, candidate, (eq, sub_iq, grams, sizes, data, tags, scale, -2*tri, roots))
    print(json.dumps({"triangle_density_exact": record,
                      "numeric_triangle_density_lower": float(fit.fun)}), flush=True)
    if F(record["rational_bound"]) >= 0:
        return None
    candidate["replay_result"] = record
    return candidate


def search(original, system, output, seconds, rounds, cut_limit, first_block, per_round,
           warm, freeze_cuts, density_if_infeasible, initial_directions,
           report_every, cut_sparsity):
    import numpy as np
    from scipy.optimize import linprog
    from scipy.sparse import csr_matrix, vstack

    A, D, grams, sizes, _, _, scale, objective, _ = system
    gram_columns = [g / scale for g in grams]
    A, D = A / scale, D / scale
    rhs = np.zeros(A.shape[0])
    rhs[0] = 1
    ld = original["linear_denominator"]
    vd = original["vector_denominator"]
    basis = original["gram_squared_vectors"]
    assert len(basis) <= len(sizes)
    basis = basis + [[] for _ in range(len(sizes) - len(basis))]
    score = objective.astype(np.float64) / 2
    for g, rank_factors, size in zip(gram_columns, basis, sizes):
        if rank_factors:
            vectors = np.asarray(rank_factors, dtype=np.float64).reshape(-1, size) / vd
            score += g @ (vectors.T @ vectors).ravel()

    started = monotonic()
    cuts, cut_rows = [], []
    if initial_directions:
        for block, values in json.loads(initial_directions.read_bytes()):
            vector = np.asarray(values, dtype=np.float64)
            assert 0 <= block < len(sizes) and vector.shape == (sizes[block],)
            cuts.append((block, vector))
            cut_rows.append(csr_matrix(-(gram_columns[block] @ np.outer(vector, vector).ravel())))
    best = None
    solver = None
    if warm:
        repo = HERE.parents[2]
        sys.path.insert(0, str(repo / "regeneration_20261105/source_full/extracted/strong_clique/flags/solver"))
        from native_highs import IncrementalLP

        solver = IncrementalLP(-score, A_eq=A, b_eq=rhs, A_ub=D,
                               b_ub=np.zeros(D.shape[0]), threads=1)
        if cut_rows:
            solver.add_inequalities(vstack(cut_rows, format="csr"), np.zeros(len(cut_rows)))
    for iteration in range(rounds + 1):
        remaining = seconds - (monotonic() - started)
        if remaining <= 0:
            break
        if solver is None:
            total_ineq = vstack([D, *cut_rows], format="csr") if cuts else D
            fit = linprog(-score, A_eq=A, b_eq=rhs, A_ub=total_ineq,
                          b_ub=np.zeros(total_ineq.shape[0]), bounds=(0, None), method="highs-ipm",
                          options={"time_limit": min(per_round, remaining)})
        else:
            found = solver.solve(time_limit=min(per_round, remaining))
            fit = SimpleNamespace(
                success=found["success"], message=found["status"], x=found["x"], fun=found["fun"],
                status=int("infeasible" in found["status"].lower()) * 2,
                eqlin=SimpleNamespace(marginals=found["equality_duals"]),
                ineqlin=SimpleNamespace(marginals=found["inequality_duals"]),
            )
        if not fit.success:
            print(json.dumps({"iteration": iteration, "error": fit.message}), flush=True)
            if fit.status == 2:
                if density_if_infeasible:
                    density = triangle_density_candidate(original, system, cuts, cut_rows, remaining)
                    if density is not None:
                        output.write_text(json.dumps(density, separators=(",", ":"))+"\n",
                                          encoding="utf-8")
                        break
                candidate = infeasibility_candidate(original, A, D, cuts, cut_rows, sizes, ld,
                                                     seconds-(monotonic()-started))
                if candidate is not None:
                    result = verify(CACHE, candidate, system)
                    print(json.dumps({"iteration": iteration, "farkas": result}), flush=True)
                    if result["rigorous_infeasible"]:
                        candidate["replay_result"] = result
                        output.write_text(json.dumps(candidate,separators=(",", ":"))+"\n",
                                          encoding="utf-8")
            break

        gram_candidates = []
        for block, (g, size) in enumerate(zip(gram_columns, sizes)):
            if block < first_block:
                continue
            matrix = (g.T @ fit.x).reshape(size, size)
            eigenvalues, eigenvectors = np.linalg.eigh((matrix + matrix.T) / 2)
            for k in np.flatnonzero(eigenvalues < -1e-8)[:2]:
                vector = eigenvectors[:, k]
                eigenvalue = float(eigenvalues[k])
                if cut_sparsity and len(vector) > cut_sparsity:
                    order = np.argsort(np.abs(vector))
                    reduced = vector.copy()
                    reduced[order[:-cut_sparsity]] = 0
                    reduced /= np.linalg.norm(reduced)
                    violation = float(reduced @ matrix @ reduced)
                    if violation < eigenvalue/4:
                        vector = reduced
                        eigenvalue = violation
                gram_candidates.append((eigenvalue, block, vector))
        gram_candidates.sort(key=lambda row: (row[0], row[1]))

        if iteration % report_every == 0 or iteration == rounds or not gram_candidates:
            candidate = dict(original)
            dual = -fit.ineqlin.marginals
            candidate["equalities"] = [round(-float(v) * ld) for v in fit.eqlin.marginals]
            candidate["inequalities"] = [max(0, round(float(v) * ld)) for v in dual[:D.shape[0]]]
            proposed = [vectors.copy() for vectors in basis]
            for weight, (block, vector) in zip(dual[D.shape[0]:], cuts):
                if weight > 0:
                    factor = [round(float(v) * sqrt(weight) * vd) for v in vector]
                    if any(factor):
                        proposed[block].append(factor)
            candidate["gram_squared_vectors"] = proposed
            result = verify(CACHE, candidate, system)
            bound = F(result["rational_bound"])
            if best is None or bound < best:
                best = bound
                candidate["replay_result"] = result
                out_tmp = output.with_name(output.name + ".partial")
                out_tmp.write_text(json.dumps(candidate, separators=(",", ":")) + "\n",
                                   encoding="utf-8")
                out_tmp.replace(output)
                print(json.dumps({"iteration": iteration, "exact": result}), flush=True)

        print(json.dumps({"iteration": iteration, "numerical": float(-fit.fun),
                          "cuts": len(cuts), "violations": len(gram_candidates),
                          "most_negative": gram_candidates[0][0] if gram_candidates else 0.,
                          "seconds": monotonic() - started}), flush=True)
        if not gram_candidates:
            break
        local_rows = []
        for _, block, vector in gram_candidates[:cut_limit]:
            cuts.append((block, vector))
            local_rows.append(csr_matrix(-(gram_columns[block] @ np.outer(vector, vector).ravel())))
        cut_rows.extend(local_rows)
        if solver is not None:
            solver.add_inequalities(vstack(local_rows, format="csr"), np.zeros(len(local_rows)))
        if freeze_cuts is not None:
            # Store the numerical rank-one search directions, not a proof.
            record = [(block, list(map(float, vector))) for block,vector in cuts]
            freeze_cuts.write_text(json.dumps(record, separators=(",", ":")), encoding="utf-8")


def run():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("start", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--vendor", type=Path)
    parser.add_argument("--shadow", action="store_true")
    parser.add_argument("--all-shadow-grams", action="store_true")
    parser.add_argument("--triangle-free-marks", action="store_true")
    parser.add_argument("--triangle-signatures", action="store_true")
    parser.add_argument("--triangle-signatures-v2", action="store_true")
    parser.add_argument("--red-clique-losses", action="store_true")
    parser.add_argument("--drop-zero-coordinates", action="store_true")
    parser.add_argument("--tree-caps", action="store_true")
    parser.add_argument("--k4-floor", action="store_true")
    parser.add_argument("--orientation-full")
    parser.add_argument("--coupled-slack", action="store_true")
    parser.add_argument("--blue-forest-zero", action="store_true")
    parser.add_argument("--anchor-override", type=F)
    parser.add_argument("--warm", action="store_true")
    parser.add_argument("--freeze-cuts", type=Path)
    parser.add_argument("--initial-directions", type=Path)
    parser.add_argument("--density-if-infeasible", action="store_true")
    parser.add_argument("--mass-low", type=F)
    parser.add_argument("--mass-high", type=F)
    parser.add_argument("--e-low", type=F)
    parser.add_argument("--e-high", type=F)
    parser.add_argument("--seconds", type=int, default=1200)
    parser.add_argument("--rounds", type=int, default=90)
    parser.add_argument("--per-round", type=int, default=180)
    parser.add_argument("--report-every", type=int, default=4)
    parser.add_argument("--cut-sparsity", type=int, default=0)
    parser.add_argument("--cut-limit", type=int, default=30)
    parser.add_argument("--first-block", type=int, default=0)
    args = parser.parse_args()
    if args.vendor:
        sys.path.insert(0, str(args.vendor))
    original = json.loads(args.start.read_bytes())
    settings = original["settings"].copy()
    if args.triangle_free_marks:
        settings["triangle_free_marks"] = True
    if args.coupled_slack:
        settings["coupled_slack"] = True
    if args.blue_forest_zero:
        assert args.drop_zero_coordinates or settings.get("drop_zero_coordinates")
        settings["blue_forest_zero"] = True
    if args.anchor_override:
        assert args.shadow
        settings["anchor_override"] = str(args.anchor_override)
    if args.triangle_signatures or args.triangle_signatures_v2:
        settings["triangle_signatures"] = True
    if args.triangle_signatures_v2:
        settings["triangle_signatures_v2"] = True
    if args.red_clique_losses:
        settings["red_clique_caps"] = True
        settings["red_clique_losses"] = True
    if args.drop_zero_coordinates:
        settings["drop_zero_coordinates"] = True
    if args.tree_caps:
        assert args.shadow
        settings["tree_caps"] = True
    if args.k4_floor:
        assert args.shadow
        settings["k4_floor"] = True
    if args.orientation_full:
        from multigraph_full_orientation import oriented_hashes

        assert not args.shadow and not args.drop_zero_coordinates
        settings["orientation_full"] = args.orientation_full
        settings["orientation_full_hashes"] = oriented_hashes(CACHE.parent / args.orientation_full)
    if args.density_if_infeasible:
        assert args.shadow and settings.get("triangle_free_marks") and not args.drop_zero_coordinates
    for key in ("mass_low", "mass_high", "e_low", "e_high"):
        if getattr(args, key) is not None:
            settings[key] = str(getattr(args, key))
    original["settings"] = settings
    if args.shadow:
        settings.setdefault("anchor_tag_depth", 1)
        if args.all_shadow_grams:
            settings["selected_shadow_blocks"] = None
        system = build_system(settings)
        original["shadow_sha256"] = shadow_hashes(SHADOW)
    else:
        assert not args.all_shadow_grams
        system = strengthened_system(CACHE, settings)
    original["projection_inputs"] = verify_projection_inputs(settings)
    search(original, system, args.output, args.seconds, args.rounds, args.cut_limit, args.first_block,
           args.per_round, args.warm, args.freeze_cuts, args.density_if_infeasible,
           args.initial_directions, args.report_every, args.cut_sparsity)


if __name__ == "__main__":
    run()
