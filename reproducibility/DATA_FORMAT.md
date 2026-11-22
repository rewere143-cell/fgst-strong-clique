# Exact data format, version 1.0.0

## Colors and labeled patterns

A pattern of order `n` has labeled positions `0,...,n-1`. Every unordered pair
has color 0 (nonedge), 1 (unmarked host edge), or 2 (marked edge). Pair `01`
always has color 2. A retained pattern is connected through positive-colored
pairs and has no two disjoint marked edges with all four cross-pairs color 0.

List pairs in lexicographic order `(0,1),(0,2),...,(n-2,n-1)`. Omit pair `01`.
If the remaining colors are `c_0,c_1,...`, the pattern code is
`sum_j c_j * 3^j`; the first omitted-root digit is the least significant digit.
No root orientation, automorphism divisor, or orbit-size factor is hidden in
this encoding. Coordinates denote the count of an individual labeled pattern,
not the sum of counts over its orbit.

## Orbit indexes and coordinates

An index entry is `-1` for an inadmissible or disconnected pattern. Otherwise
the entry is its orbit identifier under all permutations that send a marked
edge to pair `01` (including reversal of its orientation).

| File | Entries | Valid patterns | Orbits | Global coordinate numbers |
|---|---:|---:|---:|---|
| `idx3.bin` | 9 | 8 | 5 | 0 to 4 |
| `idx4.bin` | 243 | 224 | 47 | 5 to 51 |
| `idx5.bin` | 19,683 | 18,576 | 676 | 52 to 727 |
| `order6_orbit_index.bin` | 4,782,969 | 4,450,424 | 23,061 | 728 to 23,788 |

The low-order files already store global identifiers. The order-six file
stores local identifiers `0,...,23060`; add 728 to obtain global coordinates.
The two-position marked root is constant 1 and has no variable coordinate.
All indexes are signed little-endian 32-bit integers.

## Bases and Gram matrices

The first line of `basis.txt` is `N B`, here `23789 57`. Each block begins with
`k t m`, denoting the order of its labeled type, its pattern code, and the
number of selected flags. The next `m` lines contain `n c`: the order and code
of one flag in basis order. Its first `k` positions induce the indicated type.
The first flag is the type alone. Extension positions are quotiented only
by permutations that fix every type position; these flags give identical
conditional counting functions. No numerical factor accompanies deletion
of duplicate functions.

Blocks are numbered from 0. Block 0 has type order 2 and flag orders 2,3;
blocks 1 to 8 have type order 3 and flag orders 3,4; block 9 has type order 2
and flag orders 2,3,4; blocks 10 to 56 have type order 4 and flag orders 4,5.
There are 4,129 listed flags in total.

Let `offset_l = sum_{h<l} m_h^2`. A flattened matrix entry `(i,j)` of block `l`
has row number `offset_l + i*m_l + j`. All 57 complete square matrices contain
326,281 entries. They are interpreted as

```text
M_l(q) = K_l + sum_a D_l[a] q_a.
```

Only the `(0,0)` entries of the two type-order-2 blocks have constant 1;
every other entry of every `K_l` is zero. A sparse Gram key is
`flattened_row*N + coordinate`. `keys.bin` stores the increasing signed
little-endian 64-bit keys, and `values.bin` stores matching signed little-endian
32-bit positive integer coefficients. There are 1,895,405 stored nonzeros;
every absent key has coefficient zero. Both symmetric off-diagonal entries
are stored: the matrix inner product is the full trace product, without
an extra factor of one half.

## Degree equations

The first line of `degree.txt` gives the number of rows, 3,516. Each subsequent
line `k c u` specifies a connected base of order `k`, its code `c`, and the
attachment position `u`. New position `k` must have positive color to `u`.
The row sums all admissible labeled one-position extensions, accumulating
multiplicities after orbit identification. For `k>2`, subtract its base
coordinate and set the right side to 0. For `k=2`, the base is the constant
1, so there is no subtracted coordinate and the right side is 1. Thus

```text
A q = b,
A_row = extension sum - base coordinate (k>2),
b_row = 1 (k=2), otherwise 0.
```

`degree_keys.bin` stores increasing signed little-endian 64-bit keys
`row*N + coordinate`; `degree_values.bin` stores matching signed little-endian
32-bit nonzero integer coefficients. There are 433,899 stored nonzeros.

The certificate names a degree multiplier with the string
`degree_k_(2, c_0, c_1, ...)_u`. The tuple is Python's ordinary tuple notation,
including the comma in the singleton tuple `(2,)`.

## Objective and rational certificate

The objective is one half the sum of all individual labeled order-four
coordinates with pair `23` marked. When multiple such patterns share an
orbit, each occurrence contributes one half. The checker reconstructs this
vector directly from `idx4.bin` and the top base-three digit of the code.

A JSON certificate specifies positive `weight_denominator` W and
`vector_denominator` R, with `common_denominator` T = W*R^2. Each rank-one
factor has a nonnegative integer `weight_numerator` w, a zero-based `block`,
and an integer vector `vector_numerators` v. It contributes `(w/T) v v^T`
to the PSD multiplier Q of that block. Degree multipliers are the listed
`degree_weights_numerators` divided by T; absent names have multiplier 0.

The verifier reconstructs every coefficient of

```text
r = A^T lambda - sum_l D_l^*(Q_l) - o,
C = b^T lambda + sum_l trace(Q_l K_l).
```

It requires every scalar residual to be nonnegative, C=5/4 exactly, and
an empty correction map with zero correction budget. Consequently

```text
5/4 - o^T q = sum_l trace(Q_l M_l(q)) + sum_a r_a q_a.
```

`compact_certificate.json` uses T=2,400,000,000, W=24, R=10,000,
4,110 positive-weight factors and raw dual numerator 3,000,000,000.
`original_sharp_certificate.json` is an alternative certificate for
the same model. It uses R=10^12, a larger W, and 4,115 positive-weight
factors. Both give exactly 5/4 with zero correction. Each is checked
separately. The checker reads arithmetic input fields as integers or
decimal integer strings. Decimal metadata are ignored.

## Recorded results

Each run writes `summary.json`, step logs, a report on the lower-order
indices and flag bases, both certificate reports, and the finite-host
report. Each certificate report gives the numbers of positive, zero
and negative residuals and their common denominator.
