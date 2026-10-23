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
| n = (a + 1)r, m = ar, a ≥ 4, r > 0 | GL: degrees a + 2, a + 3 with multiplicities (a − 4)r², 3r². SL: degrees a + 1, a + 2, a + 3 with multiplicities t, (a − 4)r² + a + 4 − 2t, max(3r² − a − 3,0), where t = max(a + 3 − 3r²,0). | [`generic_uniform_gl_minimal_degrees`](../FD56/Hilbert/UniformGeneralGL.lean), [`generic_uniform_sl_minimal_degrees`](../FD56/Hilbert/UniformGeneralSLClassification.lean) |
| n = 4r, m = 3r, r > 0 | GL: r² degrees 6 and r² degrees 7. SL: three degrees 4 for r = 1; three degrees 5 and six degrees 6 for r = 2; r² + 8 degrees 6 and r² − 7 degrees 7 for r ≥ 3. | [UniformSmallGL](../FD56/Hilbert/UniformSmallGL.lean), [UniformThreeSLClassification](../FD56/Hilbert/UniformThreeSLClassification.lean), [GenericOneColumnSL](../FD56/Hilbert/GenericOneColumnSL.lean) |
| n = 1 | The full SL radical has m degree-zero generators for every polynomial pair. | [`scalar_slHilbert_profile`](../FD56/Hilbert/ScalarSL.lean) |

`HasMinimalKernelDegrees` contains an actual polynomial kernel basis with independent leading columns. [`hasMinimalKernelDegrees_iff_hilbert`](../FD56/Hilbert/MinimalProfile.lean) identifies its degree list with all bounded-kernel dimensions.

## Further Hilbert results

For m < n < 2m, put r = n − m and s = m − r. In every degree,
HGL(d) ≤ HSL(d) ≤ HGL(d) + d + 2.
The upper bound is attained when d ≥ floor(m/r) + floor((m + 2r)/s) + 2.
These are [`generic_middle_slHilbert_bounds` and `generic_middle_slHilbert_high`](../FD56/Hilbert/GenericMiddleSLHigh.lean). The proof constructs bounded scalar corrections using proved generic coefficient surjectivity.

For m = ar, n = (a + 1)r, r > 0, [UniformSL](../FD56/Hilbert/UniformSL.lean) proves HSL(d) = 0 for a ≥ 1 and d ≤ a. For a ≥ 4, it proves HSL(d) = HGL(d) + d + 2 for d ≥ a + 2. [UniformGeneralSLClassification](../FD56/Hilbert/UniformGeneralSLClassification.lean) proves HSL(a + 1) = max(a + 3 − 3r²,0) for every a ≥ 1. For a ≥ 4, these formulas determine every minimal degree. [UniformSLCriticalBound](../FD56/Hilbert/UniformSLCriticalBound.lean) identifies the actual critical radical with a finite polynomial relation kernel; rank-nullity gives the lower bound. [UniformPartialWitness](../FD56/Hilbert/UniformPartialWitness.lean) constructs the matching coefficient bound, which [UniformPartialSLRealization](../FD56/Hilbert/UniformPartialSLRealization.lean) realizes by an affine pair. No profile or witness assumption remains in the final theorem.

For the earlier special families, explicit affine witnesses settle the critical degree: [FamilySLRealization](../FD56/Hilbert/FamilySLRealization.lean) gives HSL(5) = k², and [UniformSLRealization](../FD56/Hilbert/UniformSLRealization.lean) gives HSL(5) = 0. Symbolic coefficient arguments work in every characteristic. [GenericKernelBound](../FD56/Hilbert/GenericKernelBound.lean) transfers their upper bounds to the universal pencil. The final family theorems retain no witness or profile assumption.

[UniformSLRelationDegree](../FD56/Hilbert/UniformSLRelationDegree.lean) extends the actual relation-kernel equivalence to all auxiliary degrees. [UniformSLHighDegree](../FD56/Hilbert/UniformSLHighDegree.lean) proves the sharp high-degree formula for a = 2,3 from d = 6. [UniformThreeSLRealization](../FD56/Hilbert/UniformThreeSLRealization.lean) settles HSL(5) for a = 3: zero for r ≥ 3 and three for r = 2, using explicit coefficient constructions over every field.

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