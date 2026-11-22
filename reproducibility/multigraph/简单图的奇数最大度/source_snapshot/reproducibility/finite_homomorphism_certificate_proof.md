# An exact finite interpretation of the marked-root certificate

This proof supplies a direct finite-graph interpretation of the same degree
and Gram matrices used by the order-six certificate. It uses color-preserving
maps that are not required to be injective. Consequently no asymptotic error,
limiting functional, subsequence, or blowup limit is needed.

## 1. Colored hosts and pullbacks

Let G be a finite simple host graph and S a nonempty strong clique of edges.
Color every pair of distinct vertices by 2 if it belongs to S, by 1 if it is
an unmarked host edge, and by 0 otherwise. Extend the color function to the
diagonal by c(v,v)=0.

A colored pattern F has distinct labeled positions, but a map f:V(F)->V(G)
may identify positions. It is color preserving if

c_F(i,j)=c_G(f(i),f(j)) for all distinct positions i,j.

Thus positions joined by a positive edge cannot be identified; positions
joined by a nonedge can be identified. Let hom(F,G) be the number of such
maps.

Every pullback pattern obtained from a map to G has the marked strong-clique
property. To check this, consider two disjoint marked edges of positions.
If their image edges are disjoint, the original strong clique supplies a
positive cross-pair. If their image edges share a vertex, a cross-pair of
positions maps to one of the two marked image edges and is positive. Hence
the forbidden four-position pattern cannot occur, even when images repeat.

This is also immediate by realizing distinct positions with the same image
as distinct independent twins in an open blowup of G. This observation is
finite and is used only to characterize allowed pullback patterns.

## 2. Finite regularization

Write Delta=maxdeg(G). Extend G to a finite simple Delta-regular graph without
increasing Delta. One explicit construction repeatedly takes two disjoint
copies and joins the corresponding copies of every deficient vertex. Each
deficient degree increases by one; vertices already of degree Delta receive
no edge. The maximum degree remains Delta, and the largest deficit decreases
by one at each iteration. After finitely many iterations the graph is
Delta-regular.

Retain the marked set S only in the original nested copy. All new edges and
all edges in copied graphs are unmarked. The original marked edges remain a
strong clique because no original host edge is removed. The marked count m
and maximum-degree parameter Delta are unchanged. Thus it suffices to prove
the target inequality in a Delta-regular host.

## 3. Exact normalized coordinates

For each connected colored pattern F on n labeled positions with marked root
edge 01, define

q_F = hom(F,G)/(2m Delta^(n-2)).

For the two-position marked-edge pattern, q=1. Every q_F lies in [0,1]: fix
the images of positions 0 and 1, for which there are exactly 2m choices, and
choose a spanning tree of F containing edge 01. Delete edge 01 and process
the remaining vertices outward from the two roots. Each new position has at
most Delta possible images because its parent edge is positive. Ignoring
all remaining color constraints only enlarges the count.

This bound does not require injectivity. It also does not require the host
order to be O(Delta).

Relabeling F, including choosing any other ordered marked edge as its root,
does not change hom(F,G). The denominator depends only on n. Therefore every
orbit identification in the program is exact for these coordinates.

## 4. Exact degree-extension equations

Fix a connected pattern F and one of its positions i. Sum over all labeled
one-position extensions F' whose new position is joined positively to i.
For each map of F there are exactly Delta choices for the new image, namely
the host neighbors of the image of i. Its colors to all existing images
determine a unique extension pattern.

If the new image equals a previously used image, the corresponding color is
0, exactly as prescribed by the diagonal convention. The extension remains
connected, and Section 1 proves it remains admissible. Thus all choices are
included in the program's extension list, and

sum_F' hom(F',G) = Delta hom(F,G).

After normalization, this is precisely sum_F' q_F'=q_F. Combining extension
patterns belonging to the same relabeling orbit produces the integer
multiplicities in the matrix A. The order-two base gives the constant right
side 1. Hence A q=b exactly, at every finite Delta.

## 5. Exact Gram identities

Let T be a connected marked-root type on k labeled positions, and let F_i be
one of the chosen extension patterns, of order n_i. For each color-preserving
map f:T->G, define

v_i(f) = number of extensions of f to F_i / Delta^(n_i-k).

The matrix

M_T = [1/(2m Delta^(k-2))] sum_{f:T->G} v(f)v(f)^T

is positive semidefinite, exactly and finitely.

To compute its ij entry, use disjoint additional position sets for F_i and
F_j, keeping their type positions identified. A pair of extension maps
determines a color on every cross-pair between their additional positions.
This includes color 0 when two new images coincide. Conversely a map of a
completed union pattern determines the two extension maps. Thus the entry
is exactly the sum of q_H over all admissible color completions H.

All such unions are connected because both component flags contain the
connected type. All realized completions are admissible by Section 1;
forbidden completions have zero maps. The normalization exponent is

(k-2)+(n_i-k)+(n_j-k)=n_i+n_j-k-2,

which is exactly the exponent used for the union pattern H. Therefore these
are precisely the program's matrices K_T+sum_j D_Tj q_j. There is no missing
binomial coefficient, automorphism divisor, or collision correction.

Keeping only one representative of extension patterns related by a
permutation of their additional positions merely deletes duplicate
functions v_i. It does not change the validity of the remaining Gram block.

## 6. Exact objective

Sum q_F over all labeled order-four patterns with 01 and 23 marked. Choosing
any two ordered marked edges of G, independently, determines a unique map of
the four positions and its unique colored pattern. The resulting pattern is
admissible and connected even if the image edges share endpoints or coincide,
by the argument in Section 1. There are (2m)^2 such pairs.

Consequently the objective used in the program is exactly

(1/2) sum_F q_F = (1/2)(2m)^2/(2m Delta^2) = m/Delta^2.

The factor 1/2 accounts for the two orientations of the second marked edge.
The orbit-merged objective simply accumulates the coefficients of the
labeled patterns in each orbit.

## 7. Apply the rational certificate

The independently verified rational data supply lambda, positive
semidefinite matrices Q_l given as nonnegative rank-one sums, and a residual
correction epsilon>=0. With

r=A^T lambda-sum_l D_l^*(Q_l)-o,
epsilon_j=max(-r_j,0),
C=b^T lambda+sum_l trace(Q_l K_l)+sum_j epsilon_j,

the exact identity is

C-o^Tq
 = sum_l trace(Q_l M_l(q))
   +sum_j (r_j+epsilon_j)q_j
   +sum_j epsilon_j(1-q_j).

Every summand is nonnegative by the finite identities and bounds proved
above. Hence m<=C Delta^2 for the regularized host, and therefore for the
original graph. Empty S and Delta=0 are trivial.

For the currently audited sharp certificate, C=5/4 exactly and every residual
coefficient r_j is nonnegative. Thus every epsilon_j is zero. The certificate
uses 4,115 explicit nonnegative rational rank-one factors. It uses the full
original matrices, with no marked-K5 exclusion and no additional domination
inequality. The construction's 91 absorption steps are already incorporated
into the valid degree multipliers lambda. The numerical solver is not trusted
by the exact verification.

Consequently m<=(5/4)Delta^2 for every finite simple host. A balanced blowup of
C5 with part size t has Delta=2t and m=5t^2, so the coefficient is sharp.

The certificate is `../flags/order6_sharp_exact_certificate.json` with SHA256
`3bcb8303cda450d975fe1cc70adcddc9800d95e53ec4b0204b379c0014a47851`.
Its independently recomputed identity is recorded in
`flag_sharp_dual_independent_verification.json`.

The four order-three defect coefficients are strictly positive, as separately
verified in `equality_defect_coefficients.json`. For Delta>0, the equality
classification in `../structure/equality_from_local_defects.md` then gives an
isolated balanced C5-blowup component containing exactly the marked edges.
The case Delta=0 is the separate trivial equality case.

## Verification boundary

This finite interpretation is a mathematical proof of the bridge from actual
graphs to the matrix constraints. Separate executable audits independently
verify all admissible six-position patterns, orbit identifications, every
degree coefficient, every Gram coefficient, and the rational dual identity.
These are exact internal checks, not external peer review or a proof-assistant
formalization. Novelty relative to the full literature is a separate issue.
