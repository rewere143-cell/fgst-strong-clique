"""Transplant a nearby SCS iterate, then refit and verify its dual."""
import argparse
from fractions import Fraction as F
import json
from pathlib import Path
import sys

from half_anchor_flag import CACHE, strengthened_system, verify_projection_inputs
from multigraph_refit_exact_dual import repair
from multigraph_weighted_maxdeg_exact import rounded_certificate


def scs_data(system, feasibility=False):
    import numpy as np
    from scipy.sparse import eye, vstack

    eq, iq, grams, sizes, _, _, scale, objective, _ = system
    packed = []
    for matrix, size in zip(grams, sizes):
        rows, columns = np.tril_indices(size)
        order = np.lexsort((rows, columns))
        rows, columns = rows[order], columns[order]
        left, right = size*rows+columns, size*columns+rows
        weights = np.where(rows == columns, 1, np.sqrt(2))/(2*scale)
        packed.append(-((matrix[:, left] + matrix[:, right]).multiply(weights)).T)
    a = vstack((eq/scale, iq/scale, -eye(len(objective)), *packed), format="csc")
    b = np.zeros(a.shape[0])
    b[0] = 1
    c = np.zeros(len(objective)) if feasibility else -objective / 2
    return dict(A=a, b=b, c=c), dict(z=eq.shape[0], l=iq.shape[0]+len(objective), s=sizes)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("starting_certificate", type=Path)
    parser.add_argument("starting_iterate", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--vendor", type=Path)
    parser.add_argument("--seconds", type=int, default=800)
    parser.add_argument("--mass-low", type=F)
    parser.add_argument("--mass-high", type=F)
    parser.add_argument("--e-low", type=F)
    parser.add_argument("--e-high", type=F)
    parser.add_argument("--exceptional-triangle-rows", action="store_true")
    parser.add_argument("--no-warm", action="store_true")
    args = parser.parse_args()
    if args.vendor:
        sys.path.insert(0, str(args.vendor))
    import numpy as np
    import scs

    original = json.loads(args.starting_certificate.read_bytes())
    settings = dict(original["settings"])
    old = strengthened_system(CACHE, settings)
    for key in ("mass_low", "mass_high", "e_low", "e_high"):
        value = getattr(args, key)
        if value is not None:
            settings[key] = str(value)
    if args.exceptional_triangle_rows:
        settings.update(k5_free=True, k5_turan=True, red_clique_caps=True,
                        red_clique_losses=True, triangle_signatures=True,
                        triangle_signatures_v2=True)
    system = strengthened_system(CACHE, settings)
    data, cones = scs_data(system)
    opt = scs.SCS(data, cones, linear_solver="qdldl", eps_abs=1e-7, eps_rel=1e-7,
                  max_iters=16000, time_limit_secs=args.seconds, verbose=True)
    if args.no_warm:
        result = opt.solve(warm_start=False)
    else:
        old_size, new_size = old[1].shape[0], system[1].shape[0]
        assert old[0].shape == system[0].shape and old[3] == system[3]
        assert old[1].shape[1] == system[1].shape[1] and new_size >= old_size
        initial = np.load(args.starting_iterate)
        y, x = initial["y"], initial["x"]
        slack = data["b"] - data["A"] @ x
        at = old[0].shape[0] + old_size
        dual = np.r_[y[:at], np.zeros(new_size-old_size), y[at:]]
        result = opt.solve(warm_start=True, x=x, y=dual, s=slack)
    path = args.output.with_suffix(".npz")
    np.savez(path, **{key: result[key] for key in ("x", "y", "s")})
    print(json.dumps(result["info"], indent=2), flush=True)
    cert = rounded_certificate(CACHE, path, "bound", settings, system)
    cert["projection_inputs"] = verify_projection_inputs(settings)
    refined = repair(CACHE, cert, 240, system)
    args.output.write_text(json.dumps(refined, separators=(",", ":"))+"\n", encoding="utf-8")
    print(json.dumps(refined["replay_result"], indent=2), flush=True)


if __name__ == "__main__":
    main()
