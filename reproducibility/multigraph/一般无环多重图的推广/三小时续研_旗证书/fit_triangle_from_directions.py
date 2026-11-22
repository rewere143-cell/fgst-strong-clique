"""Refit a triangle-mass lower bound to frozen numerical Gram directions."""
import argparse
import json
from pathlib import Path
import sys

from half_anchor_flag import verify_projection_inputs
from half_anchor_shadow import SHADOW, build_system, shadow_hashes
from rank_cut_search import triangle_density_candidate


def run():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("start", type=Path)
    parser.add_argument("directions", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--vendor", type=Path)
    parser.add_argument("--seconds", type=int, default=640)
    args = parser.parse_args()
    if args.vendor:
        sys.path.insert(0, str(args.vendor))
    import numpy as np
    from scipy.sparse import csr_matrix

    start = json.loads(args.start.read_bytes())
    settings = start["settings"]
    assert settings.get("triangle_free_marks") and not settings.get("triangle_density_objective")
    start["projection_inputs"] = verify_projection_inputs(settings)
    start["shadow_sha256"] = shadow_hashes(SHADOW)
    system = build_system(settings)
    grams, sizes, scale = system[2], system[3], system[6]
    cuts, rows = [], []
    for block, values in json.loads(args.directions.read_bytes()):
        vector = np.asarray(values, dtype=np.float64)
        assert 0 <= block < len(sizes) and vector.shape == (sizes[block],)
        cuts.append((block, vector))
        rows.append(csr_matrix(-(grams[block] / scale @ np.outer(vector, vector).ravel())))
    candidate = triangle_density_candidate(start, system, cuts, rows, args.seconds)
    if candidate is None:
        raise SystemExit("No exact positive density lower bound obtained.")
    args.output.write_text(json.dumps(candidate,separators=(",", ":"))+"\n", encoding="utf-8")


if __name__ == "__main__":
    run()
