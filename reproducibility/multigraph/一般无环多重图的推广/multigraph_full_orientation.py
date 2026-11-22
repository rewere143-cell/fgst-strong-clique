"""Exact full-system augmentation by directed extra-support moments."""

import hashlib
from math import lcm

from multigraph_orientation_cuts import hashes, load


def oriented_hashes(path):
    return hashes(path) | {".gram.npz": hashlib.sha256(path.with_suffix(".gram.npz").read_bytes()).hexdigest()}


def extend_integer(path, settings, base):
    import numpy as np
    from scipy.sparse import csr_matrix, csc_matrix, eye, hstack, load_npz, vstack

    assert oriented_hashes(path) == settings["orientation_full_hashes"]
    bounds = [settings[key] for key in ("mass_low", "mass_high", "e_low", "e_high")]
    oriented, project, identity, residue, small_scale = load(path, bounds)
    eq, iq, matrices, sizes, data, tags, base_scale, obj, roots = base
    size, more = project.shape
    assert len(tags) == size and np.array_equal(data["order"][oriented["owner"]], oriented["arity"])
    scale = lcm(base_scale, small_scale)
    initial = scale//base_scale

    def old_lift(matrix):
        return hstack((matrix*initial, csr_matrix((matrix.shape[0], more), dtype=np.int64)), format="csr")

    def new_lift(matrix, factor):
        return hstack((csr_matrix((matrix.shape[0], size), dtype=np.int64), matrix*factor), format="csr")

    home = hstack((-eye(size, dtype=np.int64), project), format="csr")*scale
    eq_out = vstack((old_lift(eq), home, new_lift(identity, scale)), format="csr")
    iq_out = vstack((old_lift(iq), new_lift(residue, scale//small_scale)), format="csr")
    gram_out = [vstack((g*initial, csc_matrix((more, g.shape[1]), dtype=np.int64)), format="csc")
                for g in matrices]
    orientation_gram = load_npz(path.with_suffix(".gram.npz")).tocsc().astype(np.int64)
    labels = (21, 21)
    at = 0
    for count in labels:
        cols = count**2
        gram_out.append(vstack((csc_matrix((size, cols), dtype=np.int64),
                                orientation_gram[:, at:at+cols]*scale), format="csc"))
        at += cols
    assert orientation_gram.shape == (more, at)
    owner = oriented["owner"]
    extras = dict(data) | {
        "order": np.r_[data["order"], oriented["arity"]],
        "aut_count": np.r_[data["aut_count"], oriented["aut"]],
        "orientation_owner": owner,
        "orientation_offset": size,
    }
    return (eq_out, iq_out, gram_out, list(sizes)+list(labels), extras,
            np.r_[tags, tags[owner]], scale, np.r_[obj, np.zeros(more, dtype=np.int64)], roots)
