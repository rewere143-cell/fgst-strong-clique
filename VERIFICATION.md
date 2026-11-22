# Verification of the restructured manuscript

The mathematical reductions, certificates, Boolean instances and verification programs supporting the manuscript are listed in the [proof index](reproducibility/multigraph/REPLAY.md). See the [release instructions](README.md) for the proof data archives.

The [version 1.2.0 build record](verification/manuscript_build_v1_2.json) identifies the complete PDF and the editing copy. Its checks cover the figure locations, internal links, page numbering and bibliography. The proof computations recorded below were run for earlier editions and use the same certificate data.

## Archived proof computations

After editing the proof and combining lemmas, we reran the [simple-graph certificate](verification/simple_uniform.json), the [weighted flag calculations](verification/multigraph_flags.log) and both [input-manifest checks](verification/multigraph_hashes.log). For the structural implication now used in Section 6, we also reran the [certificate for the absence of an induced red five-cycle](verification/absence_cycle.json). On the putative range $M\geq98/81$, the 7,692 coefficient rows give the upper bound $14802480264533669793521/12250000000000000000000<98/81$ after the 412 negative residuals are accounted for. The [verification program](reproducibility/multigraph/check_induced_five_cycle.py) tests the strict inequality using rational arithmetic. A full finite replay and the auxiliary interval checks for the previously compiled manuscript are recorded below.

| Check | Result and scope |
| --- | --- |
| Multigraph input integrity | The phase manifest matched all 1,883 listed files. These files total 4,954,016,726 bytes. All 127 entries of the supplemental manifest also matched. The two manifests can cover related inputs, so these counts are reported separately. |
| Uniform bound for simple graphs | The [replay report](verification/simple_uniform.json) records `all_passed: true` and `exact_bound: "5/4"`. The verifier reconstructed the pattern and coefficient tables, checked both the compact and original integer certificates, checked the finite test models and rejected the two deliberately altered certificates. |
| Weighted flag certificates | The multigraph flag verifier completed the five-position mass and share bounds, the five-cycle refinements, the six-position uniform chain and all eleven weighted odd-degree certificate intervals. This checks the rational inequalities for the model and side conditions specified in the manuscript. |
| Auxiliary estimates | The exact local-defect check and the fifth anchor certificate ran on the restored inputs. The integer check for a simple support in degrees 3, 5, 7 and 9 returned no unresolved shapes at the upper-bound threshold in any of the four degrees. |

## Additional replay results

The full [finite replay](verification/multigraph_finite.log) terminated with `PASS finite`. It checked the 48 degree-five formulas, the independent 21-template enumeration for degree five, the degree-seven families and both sets of order-23 cases in degree nine (18 and 112 cases). The degree-nine repeated-pair check accounted for all 114 cases, with 71 propositional refutations and 43 cases excluded by counting. The final checks covered the degree-nine and degree-eleven single-pair cases and both triangle branches for each of the two degree-nine slack families. All four final families returned empty lists of unresolved cases.

The [simple Ore calculation](verification/simple_ore.json) gave the rational bound 27332270490572378277/100000000000000000000. For the bipartite multigraph Ore bound, the [initial check](verification/ore_initial.log) gave 2989/10000. The [recursion](verification/ore_recursive.log) gave 1489/5000. The 192 entries of the recursive table and those of the [refined table](verification/ore_child_table.log) agreed with the archived values. The [final rational interval check](verification/ore_final.log) gave 2973/10000 after 73,919 splits. The combinatorial arguments that specify the constraints for these calculations are indexed in [PROOF_NOTES.md](PROOF_NOTES.md).

The input manifests also passed a [second hash check](verification/multigraph_hashes_after_replay.log) after the finite verification. The separate original proof covering all odd degrees of simple graphs is preserved for reference. Its auxiliary replay was stopped after degree 23. The current proof uses its four simple-support cases of degrees 3, 5, 7 and 9, each independently checked to completion, and the separately checked inequalities for the support.

## Reproducing the checks

Run each command in the indicated directory, with Python assertions enabled. For the simple uniform certificate, use a C17 compiler and a fresh output directory. For the multigraph flag calculations, install NumPy and SciPy. The finite checks use the bundled Windows positive-RUP checker. Its C source, the temporary storage requirements and the individual case lists are described in the [multigraph replay guide](reproducibility/multigraph/REPLAY.md).

From `reproducibility/` run

```text
python -X utf8 -B run_all.py --output results/fresh-run
```

From `reproducibility/multigraph/` run

```text
python -X utf8 -B verify.py hashes
python -X utf8 -B verify.py flags
python -X utf8 -B check_induced_five_cycle.py
python -X utf8 -B verify.py finite --jobs 2
```

The auxiliary simple-graph inputs are also available in the [fixed odd-degree archive](reproducibility/odd_degree/simple_odd_degree_fixed.zip). After extracting it, run the following command from the directory containing `check_anchored_odd_small.py`. The two gamma values and the two rounding allowances are the ones used for the simple-support check in the appendix.

```text
python -X utf8 -B check_anchored_odd_small.py --start 3 --end 9 --anchor-gamma 56425/100000 --abundance-gamma 99999/100000 --anchor-epsilon 1/1000000000 --abundance-epsilon 2/1000000000 --upper-bound-only --relax --require-complete
```

The [reproducibility guide](reproducibility/README.md) gives the full simple-graph archive replay. The [supporting proof index](PROOF_NOTES.md) identifies the combinatorial reductions that make the finite checks sufficient. The appendix gives the dependency order for the separate rational interval calculations used in the bipartite Ore bound.
