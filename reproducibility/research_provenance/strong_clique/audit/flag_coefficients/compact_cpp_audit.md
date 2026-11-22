# Cross-language compact-certificate arithmetic audit

## Result

The independent C++ verifier passes the compact certificate directly:

`flags/sharp_face/compact/compact_R10000_simple_fourdefects_certificate.json`

Certificate SHA-256:

`369542796834aa1f297dccf750f1743c8f01827d8b4ef08ef044ff474909a912`

The exact arithmetic results are:

- T = 2,400,000,000; Q = 24; R = 10,000; T = Q R².
- Raw dual numerator = 3,000,000,000.
- 4 × raw = 5 × T exactly, so the raw bound is exactly 5/4.
- 4,110 positive-weight rank-one factors, with every weight nonnegative.
- All 23,789 residuals are nonnegative; 23,590 are strictly positive.
- No correction terms are used or allowed.
- Largest residual numerator = 899,382,275,568.
- Observed maximum weight = 420,720; maximum absolute vector entry = 9,855; maximum absolute degree multiplier numerator = 251,524,241,664.

## Independence and exact computation

`verify_compact_certificate.cpp` parses the original JSON itself with a separate small JSON parser. It does not consume a Python-preprocessed certificate, import production code, invoke a solver, trust claimed residuals, or use floating-point arithmetic in any algebraic check.

It reconstructs the named degree rows directly from `degree.txt`, decodes the little-endian sparse exports explicitly, and recomputes every rank-one Gram numerator as the sum of weight × vector-entry × vector-entry. It independently constructs the objective from all labeled order-four patterns with edge23 marked, using the audited order-four orbit index.

It then recomputes

r_num = A^T lambda_num − D^*(Q_num) − T o

for every coordinate, and computes the raw numerator from the degree right side and the root-two Gram constants. It requires every residual to be nonnegative and the exact cross-multiplied bound identity to hold. The stated correction must be zero and the negative-residual correction map must be empty.

All certificate-dependent integer additions, subtractions, and multiplications use signed 128-bit integers with compiler overflow checks. Thus the observed size bounds are reported, not assumed as a substitute for checking arithmetic. Any overflow fails the verifier.

## Dependencies and scope

- Standard C++17 library only, with the explicitly requested GCC/Clang `__int128` integer extension and checked-overflow intrinsics. No third-party library is installed or used.
- The standalone JSON parser accepts the actual certificate directly. Escaped Unicode outside ASCII is deliberately unsupported and rejected; this limitation does not affect this certificate. Decimal metadata is parsed but is not used in exact algebra.
- This is an arithmetic verifier against the previously independently audited combinatorial exports. It does not reprove those exports' interpretation inside C++; the separate exhaustive coefficient checks and finite-graph tests supply that layer.
- Positive rank-one weights and positive denominator Q establish PSD exactly. No numerical eigenvalue test is involved.

## Files and reproduction

From the workspace root:

```
g++ -std=c++17 -O2 -Wall -Wextra -o strong_clique/audit/flag_coefficients/verify_compact_certificate strong_clique/audit/flag_coefficients/verify_compact_certificate.cpp
strong_clique/audit/flag_coefficients/verify_compact_certificate
```

An optional first argument selects a certificate JSON path. The default is the compact certificate above. `compact_cpp_verification.log` contains the successful summary and every positive residual numerator. `compact_cpp_input_sha256.txt` fingerprints the certificate and all consumed sparse/basis/index data.

`compact_cpp_negative_tests.json` records deliberately corrupted certificates rejected by the C++ verifier: negative rank-one weight, inconsistent denominator, perturbed degree multiplier, oversized vector integer causing checked overflow, wrong vector length, and nonzero correction. Python is used only to create these adversarial test inputs; the successful certificate is parsed directly by C++.
