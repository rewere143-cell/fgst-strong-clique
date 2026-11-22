#!/usr/bin/env python3
"""Numerical-only comparison of a native SDP dual and its C5-face projection."""
import json
from pathlib import Path
import sys
import numpy as np
from c5_face_helpers import load_face, project_to_kernel

HERE = Path(__file__).resolve().parent
BASE = HERE.parent
sys.path.insert(0, str(BASE / 'solver'))
from native_scs import smat


def main(prefix='native_sdp_01'):
    face = load_face()
    matrices = np.load(HERE / 'c5_face_data.npz')
    meta = json.loads((BASE / f'{prefix}.json').read_text())
    y = np.load(BASE / f'{prefix}.npz')['y']
    cone = meta['cone']
    assert cone['s'] == [b['size'] for b in face['blocks']]
    offset = cone['f'] + cone['l']
    records = []
    arrays = {}
    total_change2 = total_norm2 = total_complementarity = 0.0
    for block in face['blocks']:
        j, m = block['block'], block['size']
        Q = smat(y[offset:offset + m*(m+1)//2], m)
        offset += m*(m+1)//2
        ev, V = np.linalg.eigh(Q)
        L = V[:, ev > 0] * np.sqrt(ev[ev > 0])
        P = np.column_stack([project_to_kernel(v, block) for v in L.T]) if L.shape[1] else L.copy()
        clipped = L @ L.T
        projected = P @ P.T
        M = matrices[f'M_{j:03d}'] / 160
        delta = projected - clipped
        change = float(np.linalg.norm(delta))
        norm = float(np.linalg.norm(clipped))
        total_change2 += change**2
        total_norm2 += norm**2
        complementarity = float(np.sum(clipped * M))
        total_complementarity += complementarity
        arrays[f'Q_{j:03d}'] = projected
        arrays[f'L_{j:03d}'] = P
        records.append(dict(block=j, size=m, c5_rank=block['rank'],
                            clipped_dual_rank=L.shape[1],
                            input_min_eigenvalue=float(ev.min()),
                            psd_clip_frobenius=float(np.linalg.norm(clipped-Q)),
                            face_projection_frobenius=change,
                            dual_frobenius=norm,
                            relative_projection_change=change/norm if norm else 0.0,
                            clipped_complementarity= complementarity,
                            projected_complementarity=float(np.sum(projected*M)),
                            projected_factor_kernel_residual_inf=float(np.max(np.abs(M @ P))) if P.size else 0.0))
    assert offset == len(y)
    out = dict(source=prefix, numerical_only=True, sharp_upper_bound_proved=False,
               total_projection_frobenius=total_change2**0.5,
               total_dual_frobenius=total_norm2**0.5,
               relative_projection_change=(total_change2/total_norm2)**0.5,
               clipped_complementarity_total=total_complementarity,
               projected_complementarity_total=sum(b['projected_complementarity'] for b in records),
               blocks=records)
    (HERE / f'{prefix}_face_projection.json').write_text(json.dumps(out, indent=2) + '\n')
    np.savez_compressed(HERE / f'{prefix}_face_projection.npz', **arrays)
    print(json.dumps({k: v for k, v in out.items() if k != 'blocks'}, indent=2))


if __name__ == '__main__':
    main(*sys.argv[1:])
