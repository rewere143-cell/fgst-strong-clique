# Verification and Reproducibility

The programs in this directory verify the uniform bound
`ω(L(G)²) ≤ 5Δ(G)²/4`. The [fixed odd-degree archive](odd_degree/simple_odd_degree_fixed.zip)
supplies the additional certificates and finite integer checks for
the exact odd-degree bound.

## Build the manuscript

From the project root, run the following commands with a LaTeX distribution
and Latexmk.

```text
cd source
latexmk -pdf main.tex
```

The compiled manuscript is written to `source/main.pdf`.

## Verify the certificate

Use 64-bit Python 3.9 or later and a C17 compiler such as GCC or Clang
on a little-endian machine. From the project root, run

```text
cd reproducibility
python run_all.py --output results/fresh-run
```

Choose a new output directory. Use `--cc` followed by the path to the
compiler when it is outside the command search path. Run Python with
assertions enabled.

The runner checks the 12 input digests, enumerates the pattern indices and
flag bases, reconstructs the degree and Gram coefficients, and verifies
the compact and original certificates separately in exact integer arithmetic.
It also checks six finite models and two deliberately modified copies of
the compact certificate. On success,
`results/fresh-run/summary.json` records `all_passed: true` and
`exact_bound: "5/4"`. The same directory contains the individual reports.

- `data/` contains the indices, coefficients, the 4,110-factor compact
  certificate used in the manuscript, and the 4,115-factor original
  certificate. Each certificate gives the same bound for the same model.
- `verifiers/` contains the Python and C checks.
- `DATA_SHA256.json` records the byte counts and SHA-256 digests.
- [DATA_FORMAT.md](DATA_FORMAT.md) specifies the input files.
- `PROVENANCE.json` records the data's original paths and the verifier
  adaptations in archival version 1.0.0.
- `results/reference-run/` contains the original reference reports from
  that release. Its summary records the digests of the programs used in
  the archived run. A fresh run records the digests of the current programs.
- `results/revision-replay/` records the successful replay of this release.
- [research_provenance/](research_provenance/README.md) contains the
  historical coefficient generator, the recorded numerical inputs and
  code used to construct the compact certificate, and a separate C++
  verification of that certificate. These files are optional for exact
  proof replay.

## Verify the odd-degree proof

Extract `odd_degree/simple_odd_degree_fixed.zip` and enter the extracted
directory. Use the same Python and C17 environment and pass a new
output directory.

```text
python -B verify_odd_archive.py --output replay
```

The runner checks the 69 fixed inputs, replays the base model and
certificates, and checks the degree ranges and rational constants
used in the odd-degree proof. The archive's SHA-256 and the results
of a full clean-extraction replay are recorded in
[independent_replay.json](odd_degree/independent_replay.json).
