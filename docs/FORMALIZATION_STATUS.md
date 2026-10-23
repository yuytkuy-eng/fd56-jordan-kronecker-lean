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
| n = m + 1, m > 0 | SL: m degrees equal to m + 1. | [`generic_one_more_column_sl_minimal_degrees`](../FD56/Hilbert/GenericOneColumnSL.lean) |
| n = 11k, m = 8k, k > 0 | GL: degrees 5, 6, 7 with multiplicities k², 6k², 8k². SL: the same degrees with multiplicities k², 6k² + 8, 8k² − 7. | [`generic_family_gl_minimal_degrees`](../FD56/Hilbert/FamilyGL.lean), [`generic_family_sl_minimal_degrees`](../FD56/Hilbert/FamilySLClassification.lean) |
| n = (a + 1)r, m = ar, a ≥ 2, r > 0 | SL: B((a² + a + 1)r² − 1, (a − 1)r² + 1). GL is covered by the middle-range theorem above. | [`generic_uniform_middle_sl_balanced`](../FD56/Hilbert/UniformBalancedSL.lean) |
| n = 2m, m > 0 | SL: one minimal degree 3m − 1. GL polynomial kernel is zero. | [`generic_uniform_one_sl_minimal_degrees`](../FD56/Hilbert/UniformOneSLClassification.lean) |
| n = 1 | The full SL radical has m degree-zero generators for every polynomial pair. | [`scalar_slHilbert_profile`](../FD56/Hilbert/ScalarSL.lean) |

`HasMinimalKernelDegrees` contains an actual polynomial kernel basis with independent leading columns. [`hasMinimalKernelDegrees_iff_hilbert`](../FD56/Hilbert/MinimalProfile.lean) identifies its degree list with all bounded-kernel dimensions.

## Further Hilbert results

For m < n < 2m, put r = n − m and s = m − r. In every degree,
HGL(d) ≤ HSL(d) ≤ HGL(d) + d + 2.
The upper bound is attained when d ≥ floor(m/r) + floor((m + 2r)/s) + 2.
These are [`generic_middle_slHilbert_bounds` and `generic_middle_slHilbert_high`](../FD56/Hilbert/GenericMiddleSLHigh.lean). The proof constructs bounded scalar corrections using proved generic coefficient surjectivity.

[UniformClassification](../FD56/Hilbert/UniformClassification.lean) provides one theorem for every positive a,r with m = ar, n = (a + 1)r. The balanced expression above covers a ≥ 2, including all small boundary cases. The proof uses actual bounded SL relation kernels, dimension lower bounds, and explicit coefficient witnesses. [UniformSLRelationDegree](../FD56/Hilbert/UniformSLRelationDegree.lean) proves the relation-kernel equivalence in all degrees. The a = 2 finite cores are verified by exact polynomial coefficient identities over arbitrary fields. [UniformOneWitness](../FD56/Hilbert/UniformOneWitness.lean) treats n = 2m using a nilpotent cubic matrix; [UniformOneAdjugate](../FD56/Hilbert/UniformOneAdjugate.lean) supplies the matching lower bound.

For the nonuniform family (11k,8k), [FamilySLRealization](../FD56/Hilbert/FamilySLRealization.lean) proves HSL(5) = k²; the sharp high-degree formula then determines the displayed degree list. The final family theorems retain no witness or profile assumption.

[GenericDepthTwoAlpha](../FD56/Hilbert/GenericDepthTwoAlpha.lean) proves that the actual observability matrix consisting of P and PM has balanced minimal degrees with length n − 2m and sum 3m whenever n > 2m. [GenericDepthThreeAlpha](../FD56/Hilbert/GenericDepthThreeAlpha.lean) proves the analogous result for P, PM, PM², with length n − 3m and sum 6m, when n > 3m and 2n ≥ 7m. The proof realizes independently prescribed row degrees by one affine M using a surjective prefix coefficient map. These results settle the first auxiliary list in these ranges; the second list and full GL classification there remain open in this library.

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

1. The second generic auxiliary list at block depth two and above; the first auxiliary list beyond the ranges proved above; and the resulting GL degree formula when n ≥ 2m.
2. The full SL Hilbert formula in the remaining parameter regimes.
3. A formal canonical Jordan–Kronecker decomposition and identification of regular Jordan blocks. Zero polynomial kernel alone does not identify those blocks.
4. Rank-open loci and genericity on projective lines. The manuscript's Hirzebruch-surface argument and its use of the Coskun–Huizenga theorem are not formalized.

The arithmetic modules contain candidate formulas outside the proved cases. `glFormula` and `slFormula` are intended for positive n,m with 0 < n % m < m; their total Lean values elsewhere carry no classification assertion.

Every exported theorem is checked for dependencies, allowing only `propext`, `Classical.choice`, and `Quot.sound`. Passing the build certifies these Lean statements, not the full manuscript or its novelty.
