# Compact exact C5-face candidates

This directory contains compact candidates and exact arithmetic checks. It
does not replace the baseline certificate, or independently audit the finite
interpretation or coefficient generator. No public theorem claim is made here.

## Recommended small-denominator candidate

`compact_R10000_simple_fourdefects_certificate.json` passes the existing
`verify_order6_psd_certificate.py` checker at exactly **5/4**. Its saved
verification is `compact_R10000_simple_fourdefects_verification.json`.
Every factor also passes the exact C5-kernel constraints.

- Vector denominator: **10,000**.
- Weight denominator: **24**.
- Common coefficient denominator: **2,400,000,000**.
- Nonzero rank-one factors: **4,110**.
- Largest absolute vector numerator: **9,855**.
- Nonzero vector entries: **278,487**.
- Zero scalar residuals: **199**, including all 19 C5 support coordinates.
- Negative scalar residuals: **0**.
- Audited degree-row transfers: **297**.
- Largest absolute degree-multiplier numerator: **251,524,241,664**.

The deterministic gzip copy is about 476 KB, versus 4.5 MB for indented JSON.
The optional sparse JSON stores each vector as `[index,value]` pairs and is
preserved inside `redundant_candidates.tar.xz`. The preferred dense JSON stays
directly available and compatible with the existing verifier.

## Why the compatibility denominator is small

Round the native_sdp_01 factors in the exact C5 kernels. Drop the seven vectors
that round entirely to zero. Instead of changing many native factor weights,
append these two sparse integer kernel vectors:

1. Block 9: entries `(0,1), (12,-2), (47,-2)`.
2. Block 13: entries `(2,1), (21,-1)`.

Their effects on the two support-consistency equations are respectively
`(-8,8)` and `(9,1)`. Their exact added weights before common clearing are
9,202 and 17,530. The final integer weight numerators are 220,848 and 420,720;
all retained native factors have weight numerator 24.

The 17 independent support equations then determine exact degree-multiplier
corrections. Remaining negative coefficients are absorbed with existing
audited degree rows, allowing any lower-order parent whose exact C5 density
is zero. This includes marked-triangle parents as well as parents containing
unmarked edges. No new inequality is introduced: only existing equality
multipliers change. Exact C5 support residuals stay zero throughout.

## Other passes and obstructions

- Native01, reweighting two factors: R=10^6 and R=10^8 pass with the original
  unmarked-edge-only flow; their common denominators have 34 and 48 digits.
- Allowing marked-triangle flow also gives native01 passes at R=10^4 and
  R=5,000. The latter has 4,061 factors and a 23-digit common denominator.
- Native02 at R=3,000 gives 4,043 factors, 256,857 nonzero vector entries,
  236 zero residuals, and a 22-digit common denominator. Its file is
  `native_sdp_02_compact_R3000_pair0_fourdefects_certificate.json`.
  This is an exact construction pass but was not separately run through the
  standalone checker in this directory.
- Tested R=2,000 and R=1,000 native fits leave a negative coefficient only at
  order-three defect coordinate 0 after the greedy degree-row flow. This is
  an obstruction to those particular constructions, not an impossibility
  result for the scale.
- Projecting the old 43-factor refined dual is not promising: both two-factor
  reweighting and two sparse added squares leave negative coefficients at
  the four defect coordinates 0,2,3,4 and the exceptional Ferrers coordinate
  1,969. At R=10^6 the latter coefficient is exactly
  `-3281445243/4000000000` for both fits.
- Additional simple-addition trials at R=2,500,3,000,3,500,4,000,4,500,5,500,
  6,000,6,500,7,000,7,500,8,000,8,500,9,000,9,500 have no nonnegative fit using
  the two available compatibility rays. Their rounded PSD factors overshoot
  at least one compatibility target. This does not exclude altered rounding.

Each `*_result.json` contains exact pass status or explicit negative rational
coefficients. Logs preserve failed compatibility fits. Experimental failures
never overwrite a passing certificate.

## Reproduction and cache

`sweep_compact.py` builds and caches the audited model, projects native
eigenfactors into exact kernels, rounds integer factors, fits compatibility,
corrects the 17 support equations, and performs exact degree-row absorption.
`native_sdp_01_model_cache.pickle.xz` is a losslessly compressed local
computational cache only; it is not part of a proof or delivery artifact and
should be regenerated if model inputs change. The loader reads it directly
without creating an expanded pickle.

## Lossless archival and restoration

The preferred dense JSON and its gzip, all sources, all logs, and all result
summaries remain directly accessible. Other generated candidate certificates
and the optional sparse encoding are in `redundant_candidates.tar.xz`.
`ARCHIVED_DATA.json` records every original filename, byte count, SHA-256, and
compressed storage location. Every byte was read back and its hash verified
before replacing the expanded copies with compressed storage. No baseline
outside this directory was touched.

From this directory, restore every redundant candidate with:

```
tar -xJf redundant_candidates.tar.xz
```

Or restore only the optional sparse encoding:

```
tar -xJf redundant_candidates.tar.xz compact_R10000_simple_fourdefects_sparse.json
```

The cache normally needs no extraction. If an expanded pickle is wanted:

```
xz -dk native_sdp_01_model_cache.pickle.xz
```

Both commands keep the compressed originals. `compress_research_records.py`
documents the archival and verification procedure. The cache is an internal
research convenience, not a required certificate deliverable.

To reconstruct the recommended candidate with the local cache/model:

```python
from sweep_compact import prepare, attempt
attempt(prepare('native_sdp_01'), 10000, simple=True, all_defects=True)
```

To check it without relying on that cache, run from the workspace root:

```
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 python strong_clique/flags/verify_order6_psd_certificate.py sharp_face/compact/compact_R10000_simple_fourdefects_certificate.json sharp_face/compact/fresh_verification.json
```

The saved standalone verification used the existing verifier unmodified,
with its model-build function supplied the already-built cached model to
avoid another expensive enumeration. The parent independent model and finite
audits remain essential before making a public claim.
