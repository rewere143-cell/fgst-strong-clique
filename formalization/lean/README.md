# Lean Formalization of Section 2

This project formalizes the main statements in Section 2, “The Method of the Proof,” of *The Proof of the Faudree–Gyárfás–Schelp–Tuza Conjecture*. The project uses Lean 4.33.1 and its bundled libraries.

From this directory, run

```console
lake build
lake env lean CheckWeightedFlagAlgebra.lean
```

The first command builds `WeightedFlagAlgebra.lean` and its imports. The second prints the axiom dependencies of the declarations listed below. The earlier standalone prototype is in `examples/WeightedFlagAlgebraPrototype.lean`.

| Manuscript result | Lean declarations |
| --- | --- |
| Lemma 2.1 and the marked host preparation | `FiniteMultigraph.exists_regularization`, `MarkedGraph.exists_preparedHost` |
| Theorem 2.2 and its counting identity | `induced_pattern_redStrong`, `objective_eq_pattern_sum`, `objective_eq_cliqueSize`, `theorem3_2` |
| Lemma 2.3 and the identities for root densities | `root_density_pair`, `density_parameters`, `weighted_density_nonneg`, `connected_forest_density_bound`, `ForestTraversal.connected_density_bound_of_specifiedForest` |
| Theorem 2.4 and the weighted flag inequality | `FlagEntry.momentEntry_eq_sum_weightedDensity`, `NumberedFlagFamily.weightedFlagInequality` |
| Theorem 2.5 | `theorem3_5` |
| Theorem 2.6 | `theorem3_6` |
| Theorem 2.7 | `MarkedGraph.degreeFour_parallel_structure` |
| Theorem 2.8 | `degreeFour_path_density` |
| Theorem 2.9 | `MarkedGraph.theorem3_9`, derived from `MarkedGraph.degreeFour_clique_bound` |

The files retain their original Lean declaration names. Most declarations use the namespace `FGST.Chapter3`, and the flag matrix declarations use `FGST.FlagGluing`. The namespace and the numbers in names such as `theorem3_2` refer to the earlier manuscript numbering.

The Lean model represents a loopless multigraph by its symmetric adjacency multiplicities. Pattern maps may identify positions, and density counts are rational numbers. The extension identity assigns the new position index zero and shifts the old indices by one. The weighted flag inequality is stated for an ordered commutative ring equipped with a rational scalar map that sends nonnegative rationals to nonnegative elements. The proof of the degree-four interval exclusion in Lean uses the stronger bound of twenty on the size of a strong clique in maximum degree four.
