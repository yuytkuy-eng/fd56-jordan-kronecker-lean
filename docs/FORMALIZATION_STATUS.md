# Proof coverage

All theorem names below belong to the `FD56` namespace. The Lean statements are the authoritative specification of their assumptions.

| Result | Lean theorem | Scope |
| --- | --- | --- |
| Degree-five stabilizer | [`family_has_degree_five_stabilizer`](../FD56/Stabilizer/LowDegree.lean) | Any field, positive k, affine polynomial matrices of sizes 11k and 8k, with independent rows of P. Constructs X ≠ 0 and U of degree at most five with PX = 0, MX − XM = UP, and trace X = 0. |
| Balanced-profile obstruction | [`family_no_balanced_profile`](../FD56/Hilbert/HilbertObstruction.lean) | Under the same matrix assumptions, no balanced list of length 15k² + 1 and sum 97k² − 1 has the Hilbert function of the actual full SL radical. |
| Full SL radical equations | [`slRadical_iff_equations`](../FD56/Stabilizer/TraceAnnihilator.lean) | For polynomial matrices over a field and a nonempty square index type, radical membership is equivalent to trace X = 0, PX = 0, and MX − XM = UP + cI for some polynomial c. |
| Hyperplane restriction | [`hyperplane_radical_finrank`](../FD56/LinearAlgebra/HyperplaneRadical.lean), [`fieldSLRadical_finrank`](../FD56/Stabilizer/FieldRadical.lean) | Restriction of an alternating form to a hyperplane containing its radical increases the radical dimension by one. Applied to the matrix Kirillov form whenever its GL stabilizer is traceless. |
| Index recovery | [`listHilbert_determines_indices`](../FD56/Hilbert/HilbertRecovery.lean) | Equality of the functions ∑ max(0, d + 1 − e) at every nonnegative degree determines finite natural-number lists up to permutation. |
| Arbitrary-length kernel construction | [`structured_kernel`](../FD56/Stabilizer/Telescoping.lean), `structured_kernel_recovery`, `structured_kernel_injective` | The recurrence and observability equations imply the stabilizer equations. One-sided inverses imply injectivity in the coefficient matrix. [`krylov_blocks_independent`](../FD56/Stabilizer/Krylov.lean) derives independence of Krylov blocks from observability and the injective last block. Existence and degrees of the auxiliary polynomial bases remain to be established. |
| General polynomial-kernel criterion | [`bounded_polynomial_kernel_coordinates`](../FD56/LinearAlgebra/PolynomialKernel.lean) | Over an algebraically closed coefficient field, pointwise full column rank, the expected nullity over an extension field, and an injective leading matrix imply unique polynomial kernel coordinates with exact degree bounds. The proof derives Bezout coefficients, a polynomial left inverse, spanning, and predictable degrees. Verification of these matrix criteria for the GL/SL family remains separate. |
| Actual kernel Hilbert function | [`polynomial_kernel_hilbert_function`](../FD56/Hilbert/KernelDimension.lean), [`slHilbert_of_polynomial_basis`](../FD56/Hilbert/SLMatrix.lean) | The kernel criterion gives the dimension of bounded polynomial solutions as a sum of truncated degree terms. An explicit constraint matrix and a linear equivalence connect this formula to the original full SL radical and derive `HasHilbertProfile`. |
| GL dimension reduction | [`gl_block_finrank`](../FD56/Stabilizer/GLSpace.lean), [`gl_base_finrank_of_injective`](../FD56/Stabilizer/GLBase.lean) | For P = [I 0], a linear equivalence reduces the stabilizer to the smaller pair (D, B). If B has full column rank, its stabilizer has dimension r(m − r). |
| Explicit GL/SL witnesses | [`exists_gl_sl_radical_witness`](../FD56/Stabilizer/FieldRadical.lean) | At every positive block depth, explicit matrices of size n = q(r + s) + r have surjective P and radical dimensions rs for GL and rs + 1 for SL. These are pointwise examples, not a generic polynomial-pencil classification. |
| Two-degree balancing criterion | [`two_degree_tests_force_balanced`](../FD56/Hilbert/TwoDegreeCriterion.lean) | Two adjacent Hilbert values and the index sum force all indices into two adjacent degrees. Geometric realization of those values remains separate. |
| Candidate spectrum arithmetic | [`SpectrumArithmetic`](../FD56/Arithmetic/SpectrumArithmetic.lean) | List lengths, sums, block dimensions, and explicit evaluations. These are not identifications of generic spectra. |
| Numerical Hilbert branches | [`HilbertArithmetic`](../FD56/Arithmetic/HilbertArithmetic.lean) | Numerical deductions from a maximum expression. Its geometric interpretation is not established. |

## Boundaries

`TraceZeroStabilizer` is a subspace of the full `SLRadical`; they are not equated. The full SL equations include the scalar term cI.

`slHilbert` is the dimension of actual bounded polynomial radical vectors. `slHilbert_of_polynomial_basis` now derives `HasHilbertProfile` from explicit matrix rank and degree hypotheses. Verification of those hypotheses for the proposed generic spectra, and the identification with Jordan–Kronecker blocks, remain open here.

`glFormula` and `slFormula` implement the candidate nondivisible-parameter formulas. Their intended domain is positive n and m with 0 < n % m < m. Lean's total natural-number division also gives values outside that domain; those values have no asserted classification meaning. In particular, these functions do not implement the divisible Jordan cases.

## Remaining classification proofs

1. Apply the polynomial-kernel criterion to the structured GL construction; establish its pointwise ranks, nullity, and leading matrix. The abstract Hilbert-function step is proved; its application and the identification with Jordan–Kronecker blocks remain.
2. Rank-open loci, codimension estimates, and genericity on projective lines.
3. The Hirzebruch-surface bundle argument and the required application of the Coskun–Huizenga theorem.
4. Realization of generic SL extensions and the geometric Hilbert maximum formula.
5. Jordan blocks in the remaining parameter regimes and the complete generic GL/SL classification.

These gaps are not assumed as axioms. Passing the build certifies the included Lean statements, not the complete manuscript or its novelty.
