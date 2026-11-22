# Research provenance

`strong_clique/` preserves the selected upstream files in their original
relative paths. They came from `independent_review_20261103/full/strong_clique/`
in the supplied research archive. `SHA256.json` records their sizes and
digests. The [reproducibility README](../README.md) gives the offline exact
verification of the manuscript, including both fixed certificates.

Use the commands in this guide with the distributed files. The READMEs under
`strong_clique/` preserve earlier research notes and refer to paths in the
original research archive.

## Regenerate the coefficient tables

Use a writable copy of this directory on a 64-bit little-endian machine
with a C++17 compiler and the Python packages listed in
`strong_clique/flags/requirements.txt`. Run the commands below from the
directory containing `strong_clique/`. On Windows, use `.exe` for the
compiled executables.

```sh
g++ -std=c++17 -O3 strong_clique/flags/enumerate_order6.cpp -o enumerate_order6
./enumerate_order6
python -B strong_clique/audit/flag_coefficients/export_reverse_data.py
```

The enumerator writes the order-six orbit index and its representatives
under `strong_clique/flags/`. The exporter uses these files and the
recursive model builders to write the remaining binary tables and the
two basis files under `strong_clique/audit/flag_coefficients/`. The
recorded digests for the proof inputs are in [DATA_SHA256.json](../DATA_SHA256.json).
The production generator uses NumPy and SciPy. The exact replay has
separate C and Python enumeration and checks the same coefficients.
In a fresh run with GCC 15.2.0, NumPy 2.5.4 and SciPy 1.18.1, every
binary table matched its recorded digest. The two text tables matched
after changing the Windows CRLF line endings to LF.

## Trace the construction of the compact certificate

`native_sdp_01.npz` holds the recorded numerical solver output, including
its packed dual vector. `native_sdp_01.json` records the solver diagnostics.
The `sharp_face/` directory includes the recorded pentagon data and the
support projection used to turn that dual into an exact certificate.
To try the recorded scale and correction choices, first run the order-six
enumerator above and then run this command in the writable copy.

```sh
python -B -c "import os, sys; os.environ['OPENBLAS_NUM_THREADS'] = os.environ['OMP_NUM_THREADS'] = '1'; sys.path.insert(0, 'strong_clique/flags/sharp_face/compact'); from sweep_compact import attempt, prepare; result = attempt(prepare('native_sdp_01'), 10000, simple=True, all_defects=True); assert result['exact_sharp_pass']"
```

The program builds its local cache and, if successful, writes
`strong_clique/flags/sharp_face/compact/compact_R10000_simple_fourdefects_certificate.json`.
This reconstruction starts with the saved solver output. It uses a
floating-point eigendecomposition for choosing the factors, so the
generated JSON can depend on the numerical environment. For an
independent exact check, run the command below from the main
`reproducibility/` directory, replacing `PATH` with the candidate's
absolute path. The fixed certificate used in the manuscript is
distributed separately in `data/compact_certificate.json`.

```sh
python -B verifiers/check_certificate.py --certificate PATH --output candidate-check.json
```

A fresh run with Python 3.12.14, NumPy 2.5.4, SciPy 1.18.1 and
SymPy 1.14.0 produced a certificate with 4,110 factors, 199 zero
residuals and exact bound 5/4. The factors and degree multipliers
differ from those of the fixed certificate. The fresh certificate's
exact check is recorded at
[results/compact-reconstruction/candidate-check.json](../results/compact-reconstruction/candidate-check.json).

The two historical JSON reports under
`strong_clique/flags/sharp_face/compact/` record the construction and
verification of the fixed compact certificate.

## Inspect the original numerical search

The original `solve_native_sdp.py` uses `refinement_best.json` and
`refinement_best_primal.npz` to initialize the optimizer. To rerun that
script, use a writable copy on Linux with the CasADi 3.7.2 SuperSCS
headers and shared library described in
[`solver/README.md`](strong_clique/flags/solver/README.md). From the directory
containing `strong_clique/`, regenerate the order-six index as above and run:

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python -B strong_clique/flags/solve_native_sdp.py 600 1e-6 native_sdp_replay
```

This writes `native_sdp_replay.npz` and `native_sdp_replay.json` next to the
solver script. The original bridge test and its saved results are in
`strong_clique/flags/solver/test_native_scs.py` and
`strong_clique/flags/solver/validation.json`. The certificate construction
documented above starts with the shipped `native_sdp_01.npz` and can be
replayed without this optimizer.

## Run the alternate C++ check of the compact certificate

From the writable copy, copy `basis.txt`, `degree.txt`, `degree_keys.bin`,
`degree_values.bin`, `idx4.bin`, `keys.bin` and `values.bin` from
`reproducibility/data/` to `strong_clique/audit/flag_coefficients/`. Compile
the alternate verifier with a compiler supporting checked 128-bit integer
arithmetic. Pass the path to the fixed compact certificate in
`reproducibility/data/` explicitly.

```sh
g++ -std=c++17 -O2 strong_clique/audit/flag_coefficients/verify_compact_certificate.cpp -o verify_compact_certificate
./verify_compact_certificate /path/to/reproducibility/data/compact_certificate.json
```

The archived report and log in the same directory give its result. The
unbounded Python integer verifier is used for the larger original certificate.
