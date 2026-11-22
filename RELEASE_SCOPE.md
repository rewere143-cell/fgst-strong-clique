# Files covered by the release checks

The certificates, fixed Boolean instances, propositional proofs and numerical proof programs retain their archived bytes and relative paths. The data ZIPs and their members are fixed by SHA-256 in [release-data.json](release-data.json). The simple-graph odd-degree ZIP is unchanged, including its 69-input manifest. The multigraph manifests in this release cover the distributed code, data and supporting mathematical proofs. Running `verify.py hashes` checks these published manifests. The mathematical commands `flags` and `finite` run the original verification programs.

| Multigraph manifest | Original entries | Published entries | Published entries matching the archival digest |
| --- | ---: | ---: | ---: |
| Phase | 1883 | 1847 | 1847 |
| Supplemental | 127 | 127 | 125 |

The supporting proofs cited in the paper and its appendix are indexed in [PROOF_NOTES.md](PROOF_NOTES.md) and [REPLAY.md](reproducibility/multigraph/REPLAY.md). The publication omits historical progress notes outside the supporting proof references and an auxiliary script for inspecting a working directory. The release version of `REPLAY.md` describes these manifests, and the supplemental manifest records the resulting SHA-256 digest of the new phase manifest. The counts in [VERIFICATION.md](VERIFICATION.md) are the results of the original, separately recorded runs.
