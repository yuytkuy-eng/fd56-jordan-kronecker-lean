# Proof coverage

All theorem names below belong to the `FD56` namespace. The Lean statements are the authoritative specification of their assumptions.

| Result | Lean theorem | Scope |
| --- | --- | --- |
| Degree-five stabilizer | [`family_has_degree_five_stabilizer`](../FD56/Stabilizer/LowDegree.lean) | Any field, positive k, affine polynomial matrices of sizes 11k and 8k, with independent rows of P. Constructs X ≠ 0 and U of degree at most five with PX = 0, MX − XM = UP, and trace X = 0. |
| Balanced-profile obstruction | [`family_no_balanced_profile`](../FD56/Hilbert/HilbertObstruction.lean) | Under the same matrix assumptions, no balanced list of length 15k² + 1 and sum 97k² − 1 has the Hilbert function of the actual full SL radical. |
| Full SL radical equations | [`slRadical_iff_equations`](../FD56/Stabilizer/TraceAnnihilator.lean) | For polynomial matrices over a field and a nonempty square index type, radical membership is equivalent to trace X = 0, PX = 0, and MX − XM = UP + cI for some polynomial c. |
| Hyperplane restriction | [`hyperplane_radical_finrank`](../FD56/LinearAlgebra/HyperplaneRadical.lean) | A finite-dimensional alternating form restricted to a hyperplane containing its radical has radical dimension one larger. Application to the generic matrix family remains to be proved. |
| Index recovery | [`listHilbert_determines_indices`](../FD56/Hilbert/HilbertRecovery.lean) | Equality of the functions ∑ max(0, d + 1 − e) at every nonnegative degree determines finite natural-number lists up to permutation. |
| Candidate spectrum arithmetic | [`SpectrumArithmetic`](../FD56/Arithmetic/SpectrumArithmetic.lean) | List lengths, sums, block dimensions, and explicit evaluations. These are not identifications of generic spectra. |
| Numerical Hilbert branches | [`HilbertArithmetic`](../FD56/Arithmetic/HilbertArithmetic.lean) | Numerical deductions from a maximum expression. Its geometric interpretation is not established. |

## Boundaries

`TraceZeroStabilizer` is a subspace of the full `SLRadical`; they are not equated. The full SL equations include the scalar term cI.

`slHilbert` is the dimension of actual bounded polynomial radical vectors. `HasHilbertProfile` explicitly asserts its equality with an index-list formula. A Jordan–Kronecker decomposition or minimal-basis theorem establishing that equality is not yet available here.

`glFormula` and `slFormula` implement the candidate nondivisible-parameter formulas. Their intended domain is positive n and m with 0 < n % m < m. Lean's total natural-number division also gives values outside that domain; those values have no asserted classification meaning. In particular, these functions do not implement the divisible Jordan cases.

## Remaining classification proofs

1. Polynomial minimal bases, predictable degrees, and the connection to Jordan–Kronecker blocks and Hilbert functions.
2. Complete GL kernel bases, rank-open loci, and genericity on projective lines.
3. The Hirzebruch-surface bundle argument and the required application of the Coskun–Huizenga theorem.
4. Realization of generic SL extensions and the geometric Hilbert maximum formula.
5. Jordan blocks in the remaining parameter regimes and the complete generic GL/SL classification.

These gaps are not assumed as axioms. Passing the build certifies the included Lean statements, not the complete manuscript or its novelty.
