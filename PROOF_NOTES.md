# Supporting proofs for the multigraph manuscript

The indexed files retain the original proof text and their original paths under `reproducibility/multigraph/`. The [proof index](reproducibility/multigraph/REPLAY.md) also lists the fixed formulas and verification programs.

| Manuscript argument | Supporting proof |
| --- | --- |
| Forcing an induced five-cycle with all five edges red when the normalized clique size is at least 98/81 | [Proof of the bound without such a cycle](reproducibility/multigraph/一般无环多重图的推广/无全标记诱导五环的多重图上界.md), [rooted five-cycle bounds](reproducibility/multigraph/一般无环多重图的推广/多重图投影五环上界.md) and [exact verifier](reproducibility/multigraph/check_induced_five_cycle.py) |
| The exact bound for degree thirteen with slack nine | [Degree thirteen, Sections 2–5](reproducibility/multigraph/一般无环多重图的推广/七小时续研_组合归约/十三度九格锚圈的精确界.md) |
| Excluding one additional marked copy in degrees eleven and thirteen | [Simple-graph equality reduction](reproducibility/multigraph/一般无环多重图的推广/七小时续研_奇偶变换/单一重复束的简单等号归约.md) |
| Small-degree restrictions used by the weighted counts | [Degree-nine reductions](reproducibility/multigraph/一般无环多重图的推广/delta9_parallel_reduction.md) and [finite moment rows](reproducibility/multigraph/一般无环多重图的推广/七小时续研_旗证书/有限旗矩补充.md) |
| Bounds using the degree sums on the marked edges of a bipartite graph | [Matching and Ore-degree bounds](reproducibility/multigraph/一般无环多重图的推广/三小时续研_组合归约/二部剩余图的匹配与Ore锐界.md) |

The complete fixed formulas, compressed propositional proofs and verification programs are in the included [multigraph proof directory](reproducibility/multigraph/). Its [replay guide](reproducibility/multigraph/REPLAY.md) lists the files and commands for each group of degrees. The [verification record for this revision](VERIFICATION.md) reports which checks were replayed.
