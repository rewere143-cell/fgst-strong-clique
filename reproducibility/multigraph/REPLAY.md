# Loopless multigraph proof artifacts

This snapshot accompanies the English manuscript. The maximum degree and the size of a strong clique both count parallel edge occurrences. The exact bound is `D² + floor(D/2)²`.

The two multigraph integrity manifests identify the files in this release. Their scope and the relation to the original archival checks are documented in [RELEASE_SCOPE.md](../../RELEASE_SCOPE.md). The table below links the mathematical proofs to their fixed inputs and verification programs.

## Run the checks

From this directory, with Python assertions enabled, run the three commands below or run `python -B verify.py all --jobs 2`.

```text
python -B verify.py hashes
python -B verify.py flags
python -B verify.py finite --jobs 2
```

The tested Windows environment uses 64-bit Python 3.12.14, NumPy 2.5.4, SciPy 1.18.1 and the included Windows positive-RUP checker. Install NumPy and SciPy in the Python environment or pass `--vendor` and the absolute path to a directory containing them. The finite replay runs the included `d7_rup_replay.exe` and expands compressed proof files in temporary directories. Its checker source is `一般无环多重图的推广/d7_rup_replay.c`. Allow several GiB of temporary storage and reduce `--jobs` if necessary. For another operating system, the individual SAT drivers that accept `--checker` can use a compiled copy of the checker. See the [degree-seven proof](一般无环多重图的推广/delta7_parallel_reduction.md) for the compilation command.

The three commands verify file integrity, rational coefficient inequalities and finite RUP refutations, respectively. The flags command replays the five-position mass and share bounds used to start the uniform chain and the five-position exclusion of `e ≥ 1/4` for `M ≥ 4967/4000`. It then verifies the five-position cycle refinements, the six-position uniform chain, and all eleven six-position odd-degree certificates. The finite command recomputes the degree-five parallel enumeration, verifies the 48 simple degree-five refutations and 51 degree-seven parallel refutations, and checks the degree-nine reductions described below. The replays use fixed inputs and exact arithmetic. Numerical optimization and SAT solving are unnecessary.

The simple projection also uses the simple-graph theorem and equality checks. Use the parent [reproducibility guide](../README.md) to verify the simple certificates and its fixed odd-degree archive. The degree-five simple LRAT check in this snapshot regenerates the 48 fixed CNFs, compares their clauses to the archived instances, and replays their proofs. The parallel degree-five argument needs only the 21 small integer templates.

The auxiliary simple-projection inputs have their own exact replay commands. Run the local-defect check from the simple snapshot directory. Run the Ore certificate check from its `source_snapshot/ore_simple` subdirectory and give it a new report path. Both paths are relative to this snapshot.

```text
cd 简单图的奇数最大度
python -B verify_local_defect.py
cd source_snapshot/ore_simple
python -B verify_ore_certificate.py ore_plain_repaired_certificate.json ore-replay.json
```

The fifth anchor-slack certificate used in the simple equality reduction can be checked from the multigraph notes directory with `python -B check_c5_dual.py c5_anchor_column_candidate_fifth.json`.

## Proof index

| Argument used in the manuscript | Fixed proof or replay entry |
| --- | --- |
| Full degree coverage, with conventions and sharpness | [Exact theorem for loopless multigraphs](一般无环多重图的推广/一般无环多重图的强团精确界.md) |
| Five-position mass and repeated-share bounds | [Exact five-position certificates](一般无环多重图的推广/多重图五阶旗精确上界.md) |
| Projection inequalities and initial five-position refinements | [Cycle slack and marked-clique counting](一般无环多重图的推广/三小时续研_旗证书/README.md) |
| Uniform bound | [Six-position chain](一般无环多重图的推广/三小时续研_旗证书/一般多重图六阶逐步上界.md) |
| Degree three and the underlying low-degree reductions | [Multigraph reductions](一般无环多重图的推广/multigraph_bridge.md) |
| Degrees five and seven | [Degree five](一般无环多重图的推广/degree-five.md), [degree-seven parallel reduction](一般无环多重图的推广/delta7_parallel_reduction.md) |
| Old core and its degree deficits | [Five-cycle anchoring](一般无环多重图的推广/多重图五环锚定与近支撑锐界.md) |
| Joint core and outside capacity | [Joint core and outside capacity](一般无环多重图的推广/三小时续研_联立五环内外容量.md) |
| Exact odd bound for total slack three | [Exact odd bound for total slack three](一般无环多重图的推广/三小时续研_组合归约/总余量三的奇数精确界.md) |
| Odd bound for total slack at most `(D+1)/2` | [Half-degree slack and the endpoint](一般无环多重图的推广/七小时续研_组合归约/半度再加半格的奇数精确界.md) |
| Exact bounds for degree eleven with slack seven and degree fifteen with slack nine | [Degree eleven and degree fifteen](一般无环多重图的推广/七小时续研_组合归约/十一度七格与十五度九格.md) |
| Exact bound for degree thirteen with slack nine | [Degree thirteen with slack nine](一般无环多重图的推广/七小时续研_组合归约/十三度九格锚圈的精确界.md) |
| Exact bound for degree nine with slack five | [Degree nine with slack five](一般无环多重图的推广/七小时续研_组合归约/九度五格锚圈的精确界.md) |
| A single repeated marked pair | [Simple equality reduction](一般无环多重图的推广/七小时续研_奇偶变换/单一重复束的简单等号归约.md) |
| Degree nine, multiplicities and repeated roots | [Initial reduction](一般无环多重图的推广/delta9_parallel_reduction.md), [18- and 17-bundle restrictions](一般无环多重图的推广/七小时续研_奇偶变换/九度十八束及十七束的一类组合排除.md) |
| Degree nine, support of order 23 | [Triangle-free shapes](一般无环多重图的推广/三小时续研_有限度数/二十三点无标记三角形的五蓝边精确模板.md), [all order-23 branches](一般无环多重图的推广/七小时续研_有限度数/九度二十三点全部排除.md) |
| Degree nine, one or two repeated pairs and triangle-free marks | [One pair](一般无环多重图的推广/三小时续研_九度矩/九度无标记三角形的一束情形.md), [two pairs](一般无环多重图的推广/七小时续研_奇偶变换/九度无标记三角形的两束情形.md) |
| Degree nine, slack seven or nine | [32 fixed formulas](一般无环多重图的推广/七小时续研_奇偶变换/九度七格锚圈的固定核验.md), [88 fixed formulas](一般无环多重图的推广/七小时续研_奇偶变换/九度九格锚圈的固定核验.md) |
| Finite marked clique and profile rows | [Marked four-clique exclusion through degree 23](一般无环多重图的推广/七小时续研_旗证书/最大度二十一的反例无标记四团.md), [finite moment rows](一般无环多重图的推广/七小时续研_旗证书/有限旗矩补充.md) |
| Odd-degree parameter coverage and exact bounds | [Eleven certificate intervals](一般无环多重图的推广/七小时续研_旗证书/奇数度的六阶条件证书.md), [exact replay reports](一般无环多重图的推广/七小时续研_旗证书/parity_family_replayed.json) |

The positive-RUP checker verifies each added clause by unit propagation against the indicated active clauses and requires the empty clause. The finite generators encode the degree capacities and strong-clique condition in the cases identified in the proof notes. Each compressed formula is compared with its regenerated CNF where the corresponding replay supports regeneration. The degree-nine pentagon driver reports its unresolved list explicitly. The dispatcher checks that every required list is empty and that the number of cases matches the fixed inventory.

