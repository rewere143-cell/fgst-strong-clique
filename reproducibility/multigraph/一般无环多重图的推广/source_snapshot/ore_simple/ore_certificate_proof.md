# Bipartite marked Ore certificate: finite model and arithmetic

This is a separate statement from the general maximum-degree certificate.
Let G be a finite simple graph, let S be a nonempty strong clique of edges,
and suppose the graph with edge set S is bipartite. The host G need not be
bipartite. Put m=|S| and sigma=max_{uv in S}(d_G(u)+d_G(v)).

The independently verified original 47-block certificate
`ore_plain_repaired_certificate.json` has exact upper coefficient
27332270490572378277 / 100000000000000000000, approximately 0.273322704906.
In particular, it proves the clean bound **m <= (41/150) sigma^2**.
The fresh arithmetic result is `ore_plain_repaired_verification.json`.
The independent checker reconstructed every marked-bipartite column, all 3,120
inequalities, and all 47 blocks without production imports, and verified the
complete identity. Its record is `../audit/ore_repaired_dual_independent_verification.json`.
Six independent nonregular finite-host tests also passed, including an
essential same-side unmarked witness. A floating-point solver status is not proof.

The earlier `ore_plain_exact_candidate.json` is preserved as a checkpoint.
The repaired file keeps exactly the same PSD factors and refits only the
nonnegative linear-inequality multipliers.
## Stronger independently verified threshold certificate

`ore_threshold_13_50_repaired_certificate.json` proves the global coefficient
5322539332523779589 / 20000000000000000000, approximately0.26612696662619,
and hence the clean bound **m <= (4/15) sigma^2**.
It uses72 ordinary Gram blocks and3,163 inequalities. The43 extra inequalities
come from exact root-uniformity under the counterexample assumption c>=13/50.
The resulting corrected dual constant C is larger than13/50, so the global
bound is max(13/50,C)=C. The independent replay, including complete coefficient
checks, is `../audit/ore_threshold_13_50_independent_verification.json`.

This is a threshold proof, not a fixed-ratio infeasibility proof. Additional
localizing matrices and fixed-ratio experiments are separate research
extensions and are not needed for this verified4/15 conclusion.

## Retain all witnesses, then prune irrelevant vertices

Replace G by its induced graph on the endpoints of S. Every witness edge
between two disjoint marked edges has both endpoints in this set, so S remains
a strong clique. Keep every host edge on that set, including unmarked edges
whose endpoints lie on the same side of the marked bipartition. The new Ore
parameter sigma' is at most sigma. Prove the bound with sigma'; it implies the
original bound. Every remaining vertex v has a marked neighbor w, hence
its new degree is at most sigma'-1. No regularization is performed.

## Finite, noninjective color maps

Use three colors: 0 for absent edges, 1 for unmarked host edges, and 2 for
marked edges. The host diagonal has color 0. Maps preserve every pair color,
including color 0, but may identify nonadjacent domain vertices. A pattern is
admissible if it has no two disjoint marked domain edges without a positive
host-color cross pair. Images of overlapping marked edges also satisfy this
condition, because an endpoint of one image is adjacent to the other endpoint
of the other image. Thus every induced pattern of a valid map is admissible.

For a connected k-vertex pattern F with the ordered root 01 marked, define

q_F = hom_color(F,G)/(2m (sigma')^(k-2)).

Whole-label relabeling and re-rooting at any marked edge leave this quantity
unchanged. A spanning tree containing the root edge gives 0<=q_F<=1, because
every remaining vertex has at most sigma' host neighbors. This argument does
not bound the total number of host vertices or unmarked host edges.

The marked graph of every image pattern is bipartite. Conversely, we exclude
only patterns whose color-2 graph is not bipartite; no constraint is imposed
on the bipartiteness of the color-1-or-2 host graph.

## Exact objective and valid linear inequalities

The objective is one half of the sum of q_F over all ordered four-label
patterns with 01 and 23 marked. It equals m/(sigma')^2 exactly: this counts two
independently chosen ordered marked edges, including shared or repeated images.

For each connected base pattern and each distinguished vertex, sum all
one-vertex extensions whose new vertex is host-adjacent to that vertex. This
sum is at most q_F. If uv is a marked base edge, the sum of the two extension
sums at u and v is at most q_F, because d_G(f(u))+d_G(f(v))<=sigma'. Common
neighbors are counted twice, as required by the degree sum. In particular,
subtract the base coordinate once, not twice, in the Ore inequality.

These are A q <= b. Every degree/Ore multiplier in a valid dual must be
nonnegative. Arbitrary-signed multipliers from the general regular-host model
cannot be used here.

## Exact Gram identities

Condition on a marked ordered type embedding and count color-preserving
extensions of each basis flag, normalized by powers of sigma'. Products are
expanded over every cross-pair color. Average only after taking the conditional
outer product. Each block M_l=K_l+D_l q is positive semidefinite exactly.

Restricting to marked-bipartite variables is valid because all other coordinates
vanish. Removing basis rows with an identically zero diagonal takes a principal
submatrix. The original Ore certificate uses 47 surviving blocks from the 57
independently audited general blocks. Additional non-marked-root type blocks
are a separate optional model and are recorded explicitly in its certificates.

## Exact dual identity

The certificate records rational lambda>=0 and PSD matrices Q_l as explicit
sums of nonnegative rational rank-one outer products. Define

r=A^T lambda - sum_l D_l^*(Q_l) - o,
epsilon_i=max(-r_i,0),
C=lambda^T b + sum_l tr(Q_l K_l) + sum_i epsilon_i.

Then the following identity is exact:

C-o^T q = lambda^T(b-Aq) + sum_l tr(Q_l M_l)
          + sum_i (r_i+epsilon_i)q_i + sum_i epsilon_i(1-q_i).

Every term on the right is nonnegative. Therefore m/(sigma')^2<=C and hence
m<=C sigma^2 for the original graph. The verifier uses only integer arithmetic
for this identity. Floating-point optimization is used only to discover the
candidate factors and multipliers; its residual is fully paid by epsilon.

## Reproduction

From the workspace root, with the recorded Python dependencies:

- `python strong_clique/flags/certify_ore_sdp.py ore_native_plain_900 ore_plain_exact_candidate.json`
- `python strong_clique/flags/repair_ore_certificate.py ore_plain_exact_candidate.json ore_plain_repaired_certificate.json`
- `python strong_clique/flags/verify_ore_certificate.py ore_plain_repaired_certificate.json ore_plain_repaired_verification.json`

The native solver input is retained, but no solver is required for verification.
Use `--extra` only for certificates produced by the optional extra-type model;
the verifier reads this distinction from the certificate metadata.
