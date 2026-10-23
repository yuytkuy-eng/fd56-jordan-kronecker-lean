# Proof coverage

The library is a partial formalization. Its final results describe actual reduced polynomial kernel bases. The complete generic Jordan–Kronecker classification remains unfinished.

Here **generic** means the universal affine pair over the rational function field of its independent coefficients. The final degree theorems below hold over every base field. They do not assert a generic rational specialization over every field. Lean statements give the exact size and positivity assumptions.

## Established minimal degrees

Write B(D,R) for the balanced list of R nonnegative integers with sum D. Multiplicities count basis vectors; n is the square-matrix size and m is the number of rows of P. All theorem names belong to `FD56`.

| Parameters | Proved result | Source |
| --- | --- | --- |
| m > n, s = m − n | GL: n copies of B(n,s). For n > 0, SL: B(n² − 1,ns + 1). | [`generic_above_gl_minimal_degrees`, `generic_above_sl_minimal_degrees`](../FD56/Hilbert/GenericMinimal.lean) |
| m = n | GL kernel zero. For n > 0, SL has one degree n − 1. | [`generic_square_gl_minimal_degrees`, `generic_square_sl_minimal_degrees`](../FD56/Hilbert/GenericMinimal.lean) |
| n = (q + 1)m, m > 0 | GL polynomial kernel zero. | [`generic_divisible_gl_kernel_hilbert`](../FD56/Hilbert/DivisibleGL.lean) |
| m < n < 2m; r = n − m, s = m − r | GL: all αᵢ + βⱼ + 1, where α = B(m,r) and β = B(m + 2r,s). Both auxiliary lists and polynomial spanning are proved. | [`generic_middle_gl_minimal_degrees`](../FD56/Hilbert/GenericMiddle.lean) |
| 2m < n < 3m; r = n − 2m, s = m − r | GL: all αᵢ + βⱼ + 2, where α = B(3m,r) and β = B(3m + 3r,s). Both auxiliary lists and polynomial spanning are proved. | [`generic_depth_two_gl_minimal_degrees`](../FD56/Hilbert/GenericDepthTwoGL.lean) |
| m < n, 2n ≤ 3m | Complete SL degree list, including every uniform and nonuniform case in this range. | [`generic_middle_sl_minimal_degrees_of_twice_le`](../FD56/Hilbert/MiddleSLClassification.lean) |
| n = 2m − 1, m ≥ 2 | SL: m degrees equal to 3m − 3. | [`generic_near_double_sl_minimal_degrees`](../FD56/Hilbert/MixedOneSingleHighSL.lean) |
| n = 2m, m > 0 | SL: one degree 3m − 1. GL polynomial kernel is zero. | [`generic_uniform_one_sl_minimal_degrees`](../FD56/Hilbert/UniformOneSLClassification.lean) |
| n = 1 | The full SL radical has m degree-zero generators for every polynomial pair. | [`scalar_slHilbert_profile`](../FD56/Hilbert/ScalarSL.lean) |

`HasMinimalKernelDegrees` contains an actual polynomial kernel basis with independent leading columns. [`hasMinimalKernelDegrees_iff_hilbert`](../FD56/Hilbert/MinimalProfile.lean) identifies its degree list with all bounded-kernel dimensions.

For the SL range 2n ≤ 3m, write r = n−m, a = floor(m/r), v = m mod r, and u = r−v. Thus a ≥ 2 and u > 0. If v = 0, the list is B((a²+a+1)r²−1, (a−1)r²+1), proved in [UniformBalancedSL](../FD56/Hilbert/UniformBalancedSL.lean). If v > 0, use the following table.

| Case | D | A | B | C |
| --- | --- | --- | --- | --- |
| a ≥ 4; g = (a−4)r+v | a+2 | ug | 3ur+vg | 3vr |
| a = 3 | 6 | u(u+3v) | u²+uv+3v² | uv |
| a = 2, u ≤ v | 5 | u(v−u) | 2u²+v² | v(2u+v) |
| a = 2, v < u | 6 | 3uv | u(u−v)+3v² | v(u−v) |

The GL degrees D, D+1, D+2 have multiplicities A, B, C. Put t = max(D+2−C,0). The SL multiplicities at those degrees are A+t, B+D+3−2t, max(C−D−2,0). [MiddleSLClassification](../FD56/Hilbert/MiddleSLClassification.lean) combines the branches with no witness assumptions. For example, (n,m) = (11k,8k) has GL multiplicities k², 6k², 8k² at degrees 5,6,7, and SL multiplicities k², 6k²+8, 8k²−7.

## Further Hilbert results

For m < n < 2m, put r = n − m and s = m − r. In every degree,
HGL(d) ≤ HSL(d) ≤ HGL(d) + d + 2.
The upper bound is attained when d ≥ floor(m/r) + floor((m + 2r)/s) + 2.
These are [`generic_middle_slHilbert_bounds` and `generic_middle_slHilbert_high`](../FD56/Hilbert/GenericMiddleSLHigh.lean). The proof constructs bounded scalar corrections using proved generic coefficient surjectivity.

The SL proofs use bounded relation kernels, dimension lower bounds, and explicit polynomial coefficient witnesses. [MixedPolynomialWitness](../FD56/Hilbert/MixedPolynomialWitness.lean) transfers bounded scalar obstructions to the same generic auxiliary matrix whose kernel ranks are proved independently. [MixedSLGeneralRealization](../FD56/Hilbert/MixedSLGeneralRealization.lean) realizes it as an actual affine pair. The small cores in dimensions (9,7) and (10,7) are verified by coefficient identities valid over every field. [MixedOneSingleHighWitness](../FD56/Hilbert/MixedOneSingleHighWitness.lean) supplies a polynomial chain for n = 2m−1; [UniformOneWitness](../FD56/Hilbert/UniformOneWitness.lean) and [UniformOneAdjugate](../FD56/Hilbert/UniformOneAdjugate.lean) treat n = 2m.

[GenericDepthTwoAlpha](../FD56/Hilbert/GenericDepthTwoAlpha.lean) proves that the actual stack P, PM has balanced minimal degrees with length n − 2m and sum 3m whenever n > 2m. In the range 2m < n < 3m, [DepthTwoBetaWitness](../FD56/Hilbert/DepthTwoBetaWitness.lean) constructs an actual affine pair attaining the second auxiliary dimension bound. A transcendental deformation preserves the first stack kernel and transfers coefficient ranks from a prescribed terminal matrix. [GenericDepthTwoBeta](../FD56/Hilbert/GenericDepthTwoBeta.lean) then proves the second list without witness assumptions. [DepthTwoGL](../FD56/Hilbert/DepthTwoGL.lean) proves polynomial spanning and leading independence for the resulting GL basis, giving the complete list in the table.

[GenericDepthThreeAlpha](../FD56/Hilbert/GenericDepthThreeAlpha.lean) proves the analogous first auxiliary result for P, PM, PM², with length n − 3m and sum 6m, for every n > 3m. [DepthThreeAlphaWitness](../FD56/Hilbert/DepthThreeAlphaWitness.lean) constructs the affine witness by lifting through the kernel of an independent linear/quadratic prefix and then deforming its action. The proof transfers the third-stack bound from independent rows of degrees 1, 2, and 3. Its second auxiliary list and full GL classification remain open in this library.

The earlier [`family_no_balanced_profile`](../FD56/Hilbert/HilbertObstruction.lean) also applies directly to affine pairs of sizes (11k,8k) with independent rows of P; it is not restricted to the universal pencil.

## Supporting proofs

- [MinimalBasis](../FD56/Hilbert/MinimalBasis.lean) proves existence of reduced bases for every finite polynomial matrix kernel. [MinimalIndices](../FD56/Hilbert/MinimalIndices.lean) proves uniqueness of the degree multiset from its Hilbert function.
- [DualPrescribed](../FD56/LinearAlgebra/DualPrescribed.lean) and [PrescribedDegrees](../FD56/Hilbert/PrescribedDegrees.lean) construct complementary reduced polynomial bases with prescribed degree lists of equal sum.
- [GenericPencil](../FD56/Stabilizer/GenericPencil.lean) proves generic GL/SL radical dimensions. [GenericRows](../FD56/Stabilizer/GenericRows.lean) supplies polynomial right inverses and leading-rank proofs for generic rectangular pencils.
- [MiddleSLReduction](../FD56/Stabilizer/MiddleSLReduction.lean) retains the full equation MX − XM = UP + cI. [MiddleSLHilbert](../FD56/Hilbert/MiddleSLHilbert.lean) proves HSL = HGL + dimension of the bounded scalar image. The traceless GL stabilizer is not identified with the full SL radical.
- [StructuredGL](../FD56/Hilbert/StructuredGL.lean) gives a general-depth criterion with explicit auxiliary-basis, recurrence, rank, and degree hypotheses. [ObservabilityRealization](../FD56/Stabilizer/ObservabilityRealization.lean) realizes matrix families as P, PM, … under an explicit coefficient-surjectivity hypothesis. Their remaining generic hypotheses are not silently discharged.
- [RankSpecializationExtension](../FD56/LinearAlgebra/RankSpecializationExtension.lean) transfers rank bounds from arbitrary field specializations. [GenericKernelExtension](../FD56/Hilbert/GenericKernelExtension.lean) permits affine witnesses over field extensions without requiring a coefficient-ring section.
- [KroneckerSum](../FD56/Hilbert/KroneckerSum.lean), [BlockSum](../FD56/Hilbert/BlockSum.lean), and [ConstantEquivalence](../FD56/Hilbert/ConstantEquivalence.lean) prove bounded-kernel formulas for supplied blocks and invariance under supplied constant equivalences.

## Remaining work

1. The second generic auxiliary list at block depth three and above; the first auxiliary list beyond the ranges proved above; and the resulting GL degree formula when n ≥ 3m outside the divisible families.
2. The SL Hilbert formula for the remaining cases with 3m < 2n, excluding n = 2m−1 and n = 2m.
3. A formal canonical Jordan–Kronecker decomposition and identification of regular Jordan blocks. Zero polynomial kernel alone does not identify those blocks.
4. Rank-open loci and genericity on projective lines. The manuscript's Hirzebruch-surface argument and its use of the Coskun–Huizenga theorem are not formalized.

The arithmetic modules contain candidate formulas outside the proved cases. `glFormula` and `slFormula` are intended for positive n,m with 0 < n % m < m; their total Lean values elsewhere carry no classification assertion.

Every exported theorem is checked for dependencies, allowing only `propext`, `Classical.choice`, and `Quot.sound`. Passing the build certifies these Lean statements, not the full manuscript or its novelty.
