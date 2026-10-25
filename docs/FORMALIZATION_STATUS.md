# Proof coverage

The library is a partial formalization. Its final results describe actual reduced polynomial kernel bases. The complete generic Jordan–Kronecker classification remains unfinished.

Here **generic** means the universal affine pair over the rational function field of its independent coefficients. The final degree theorems below hold over every base field unless a characteristic-zero assumption is stated. They do not assert a generic rational specialization over every field. Lean statements give the exact size and positivity assumptions.

## Established minimal degrees

Write B(D,R) for the balanced list of R nonnegative integers with sum D. Multiplicities count basis vectors; n is the square-matrix size and m is the number of rows of P. All theorem names belong to `FD56`.

| Parameters | Proved result | Source |
| --- | --- | --- |
| m > n, s = m − n | GL: n copies of B(n,s). For n > 0, SL: B(n² − 1,ns + 1). | [`generic_above_gl_minimal_degrees`, `generic_above_sl_minimal_degrees`](../FD56/Hilbert/GenericMinimal.lean) |
| m = n | GL kernel zero. For n > 0, SL has one degree n − 1. | [`generic_square_gl_minimal_degrees`, `generic_square_sl_minimal_degrees`](../FD56/Hilbert/GenericMinimal.lean) |
| n = (q + 1)m, m > 0 | GL polynomial kernel zero. | [`generic_divisible_gl_kernel_hilbert`](../FD56/Hilbert/DivisibleGL.lean) |
| m < n < 2m; r = n − m, s = m − r | GL: all αᵢ + βⱼ + 1, where α = B(m,r) and β = B(m + 2r,s). Both auxiliary lists and polynomial spanning are proved. | [`generic_middle_gl_minimal_degrees`](../FD56/Hilbert/GenericMiddle.lean) |
| 2m < n < 3m; r = n − 2m, s = m − r | GL: all αᵢ + βⱼ + 2, where α = B(3m,r) and β = B(3m + 3r,s). Both auxiliary lists and polynomial spanning are proved. | [`generic_depth_two_gl_minimal_degrees`](../FD56/Hilbert/GenericDepthTwoGL.lean) |
| n = 7k, m = 2k, k > 0; characteristic zero | GL: k² degrees equal to 31. The auxiliary lists have k copies of 12 and k copies of 16. | [`generic_seven_two_repeated_gl_minimal_degrees`](../FD56/Hilbert/DepthThreeSevenTwoFamily.lean) |
| n = 11k, m = 3k, k > 0; characteristic zero | GL: 2k² degrees equal to 38. The auxiliary lists have 2k copies of 9 and k copies of 26. | [`generic_eleven_three_repeated_gl_minimal_degrees`](../FD56/Hilbert/DepthThreeElevenThreeFamily.lean) |
| m < n, 2n ≤ 3m | Complete SL degree list, including every uniform and nonuniform case in this range. | [`generic_middle_sl_minimal_degrees_of_twice_le`](../FD56/Hilbert/MiddleSLClassification.lean) |
| 3m < 2n, n < 2m | Complete SL Hilbert function and every minimal-degree multiplicity, over every field. | [`generic_mixed_one_slHilbert_closed`](../FD56/Hilbert/MixedOneSLHilbert.lean), [`generic_mixed_one_sl_minimal_multiplicities`](../FD56/Hilbert/MixedOneSLClassification.lean) |
| n = 2m − 3, m ≥ 4; characteristic zero | SL: B(3(m−2)(m−1)+2, 3m−8). | [`generic_third_near_double_sl_minimal_degrees_all`](../FD56/Hilbert/MixedOneThreeSLClassification.lean) |
| n = 2m − 2, m ≥ 5; characteristic zero | SL: B(3(m−1)², 2m−3). | [`generic_second_near_double_sl_minimal_degrees`](../FD56/Hilbert/MixedOneTwoSLClassification.lean) |
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

For the remaining middle range, put u = 2n−3m and v = 2m−n, so m = u+2v and n = 2u+3v with u,v > 0. Write [x]₊ = max(x,0). In every nonnegative degree d the SL Hilbert function is

H(d) = max(u[v(d−1)−(3u+4v)]₊ + v[v(d−2)−(3u+4v)]₊, [((u+v)v+1)d+2−(3u²+8uv+6v²)]₊).

Set H(d)=0 for negative d. The multiplicity of minimal degree k is H(k)−2H(k−1)+H(k−2). `generic_mixed_one_sl_minimal_multiplicities` proves this formula for an actual reduced polynomial kernel basis. This also determines the near-double families over arbitrary characteristic; the earlier dedicated balanced-list theorems in the table retain their original characteristic-zero hypotheses.

## Further Hilbert results

For m < n < 2m, put r = n − m and s = m − r. In every degree,
HGL(d) ≤ HSL(d) ≤ HGL(d) + d + 2.
The upper bound is attained when d ≥ floor(m/r) + floor((m + 2r)/s) + 2.
These are [`generic_middle_slHilbert_bounds` and `generic_middle_slHilbert_high`](../FD56/Hilbert/GenericMiddleSLHigh.lean). The proof constructs bounded scalar corrections using proved generic coefficient surjectivity.

The SL proofs use bounded relation kernels, dimension lower bounds, and explicit polynomial coefficient witnesses. [MixedPolynomialWitness](../FD56/Hilbert/MixedPolynomialWitness.lean) transfers bounded scalar obstructions to the same generic auxiliary matrix whose kernel ranks are proved independently. [MixedSLGeneralRealization](../FD56/Hilbert/MixedSLGeneralRealization.lean) realizes it as an actual affine pair. The small cores in dimensions (9,7) and (10,7) are verified by coefficient identities valid over every field. [MixedOneSingleHighWitness](../FD56/Hilbert/MixedOneSingleHighWitness.lean) supplies a polynomial chain for n = 2m−1; [UniformOneWitness](../FD56/Hilbert/UniformOneWitness.lean) and [UniformOneAdjugate](../FD56/Hilbert/UniformOneAdjugate.lean) treat n = 2m.

[GenericDepthTwoAlpha](../FD56/Hilbert/GenericDepthTwoAlpha.lean) proves that the actual stack P, PM has balanced minimal degrees with length n − 2m and sum 3m whenever n > 2m. In the range 2m < n < 3m, [DepthTwoBetaWitness](../FD56/Hilbert/DepthTwoBetaWitness.lean) constructs an actual affine pair attaining the second auxiliary dimension bound. A transcendental deformation preserves the first stack kernel and transfers coefficient ranks from a prescribed terminal matrix. [GenericDepthTwoBeta](../FD56/Hilbert/GenericDepthTwoBeta.lean) then proves the second list without witness assumptions. [DepthTwoGL](../FD56/Hilbert/DepthTwoGL.lean) proves polynomial spanning and leading independence for the resulting GL basis, giving the complete list in the table.

[GenericDepthThreeAlpha](../FD56/Hilbert/GenericDepthThreeAlpha.lean) proves the analogous first auxiliary result for P, PM, PM², with length n − 3m and sum 6m, for every n > 3m. [DepthThreeAlphaWitness](../FD56/Hilbert/DepthThreeAlphaWitness.lean) constructs the affine witness by lifting through the kernel of an independent linear/quadratic prefix and then deforming its action. The proof transfers the third-stack bound from independent rows of degrees 1, 2, and 3. Its second auxiliary list remains open in general; two characteristic-zero families are proved below.

[GenericDepthThreeRightInverse](../FD56/Hilbert/GenericDepthThreeRightInverse.lean) also proves coefficient surjectivity, a polynomial right inverse of degree at most 6m, and independent leading rows for this third stack.

[MixedOneTwoSLClassification](../FD56/Hilbert/MixedOneTwoSLClassification.lean) treats the characteristic-zero family n = 2m−2. Explicit completions in sizes (6,4) and (8,5) start a cubic extension that adds two rows at each step. The extension preserves a reduced two-row kernel and propagates the scalar obstruction in the two critical degrees. A bounded affine realization transfers these obstructions to the generic SL equation. Hilbert-function convexity then determines every minimal degree. The smaller cases m = 3,4 already belong to the range 2n ≤ 3m proved over every field.

The earlier [`family_no_balanced_profile`](../FD56/Hilbert/HilbertObstruction.lean) also applies directly to affine pairs of sizes (11k,8k) with independent rows of P; it is not restricted to the universal pencil.

[MixedOneLowerEnvelope](../FD56/Hilbert/MixedOneLowerEnvelope.lean) supplies the lower bound used in the quotient-one proof. [MixedOneSLHilbert](../FD56/Hilbert/MixedOneSLHilbert.lean) proves equality in every degree. The infinite family m = 2v+1, n = 3v+2, v ≥ 4 still excludes balanced SL degrees: HGL(6) = v−3 > 0, whereas the proposed balanced list has no generators in degree 6.

[MixedOneThreeSLClassification](../FD56/Hilbert/MixedOneThreeSLClassification.lean) treats the characteristic-zero family n = 2m−3. Three finite completions start the cubic extension in the three residue classes of m; a fourth handles the exceptional initial case (m,n) = (7,11). Explicit coefficient identities establish the scalar obstructions, and [UniformCubicCompletion](../FD56/Hilbert/UniformCubicCompletion.lean) propagates them together with a reduced three-row kernel. This gives the critical Hilbert bounds and hence the complete degree list. The smaller cases m = 4,5,6 already belong to the range 2n ≤ 3m.

## Supporting proofs

- [MinimalBasis](../FD56/Hilbert/MinimalBasis.lean) proves existence of reduced bases for every finite polynomial matrix kernel. [MinimalIndices](../FD56/Hilbert/MinimalIndices.lean) proves uniqueness of the degree multiset from its Hilbert function.
- [DualPrescribed](../FD56/LinearAlgebra/DualPrescribed.lean) and [PrescribedDegrees](../FD56/Hilbert/PrescribedDegrees.lean) construct complementary reduced polynomial bases with prescribed degree lists of equal sum.
- [GenericPencil](../FD56/Stabilizer/GenericPencil.lean) proves generic GL/SL radical dimensions. [GenericRows](../FD56/Stabilizer/GenericRows.lean) supplies polynomial right inverses and leading-rank proofs for generic rectangular pencils.
- [MiddleSLReduction](../FD56/Stabilizer/MiddleSLReduction.lean) retains the full equation MX − XM = UP + cI. [MiddleSLHilbert](../FD56/Hilbert/MiddleSLHilbert.lean) proves HSL = HGL + dimension of the bounded scalar image. The traceless GL stabilizer is not identified with the full SL radical.
- [StructuredGL](../FD56/Hilbert/StructuredGL.lean) gives a general-depth criterion with explicit auxiliary-basis, recurrence, rank, and degree hypotheses. [ObservabilityRealization](../FD56/Stabilizer/ObservabilityRealization.lean) realizes matrix families as P, PM, … under an explicit coefficient-surjectivity hypothesis. Their remaining generic hypotheses are not silently discharged.
- [GenericTerminalObservability](../FD56/Hilbert/GenericTerminalObservability.lean) proves injectivity of the generic terminal stack at every depth q when qm ≤ n ≤ (q+1)m. The next block is therefore injective on the preceding stack's polynomial kernel. This does not determine its minimal degrees or prove polynomial right-invertibility.
- [ObservabilityGLNormalForm](../FD56/Hilbert/ObservabilityGLNormalForm.lean) proves at arbitrary depth that a GL kernel vector annihilates the preceding observability kernel when the terminal stack is injective. A supplied right inverse then gives row factorization and the auxiliary beta relation. The right-inverse hypotheses remain explicit; these lemmas do not supply the missing higher-depth degree lists.
- [ObservabilityGLReduction](../FD56/Hilbert/ObservabilityGLReduction.lean) gives an exact, unique polynomial parameterization at every positive depth. Writing O for the preceding stack, V for its kernel basis matrix, and R for a supplied right inverse, the parameter A satisfies PA = 0, AOMV = 0, and MA − AOMR = UPR, with X = AO. The converse is proved as well. Generic terminal injectivity is discharged, while the basis and right inverse remain explicit inputs. This reduction does not determine the higher-depth minimal degrees.
- [ObservabilityGLRecurrence](../FD56/Hilbert/ObservabilityGLRecurrence.lean) propagates observability constraints through a supplied coefficient recurrence and factors its terminal coefficient through the preceding kernel basis, with a unique auxiliary parameter when the beta condition holds.
- [DepthThreeGLNormalForm](../FD56/Hilbert/DepthThreeGLNormalForm.lean) derives this terminal factorization directly from the depth-three GL equations, a supplied third-stack kernel basis and right inverse, and fourth-stack injectivity. The terminal coefficient is VE for a unique E satisfying E(PM³V) = 0. The proof establishes the two required coefficient recurrences; it does not assume them.
- [DepthThreeGLReconstruction](../FD56/Hilbert/DepthThreeGLReconstruction.lean) reconstructs every GL solution from E and its unique row-relation coefficients. [DepthThreeGLBasis](../FD56/Hilbert/DepthThreeGLBasis.lean) constructs an actual polynomial GL kernel basis indexed by the product of the two auxiliary basis index sets, with explicit columns and a bijective coordinate map. For 3m < n ≤ 4m, `generic_depth_three_gl_kernel_basis` supplies the right inverse and terminal injectivity from the generic pair. Both auxiliary bases remain inputs; their existence is distinct from their degree lists. [DepthThreeGL](../FD56/Hilbert/DepthThreeGL.lean) proves reducedness and the degree formula below. The second generic auxiliary degree list remains open at depth three outside the families below.
- [StackedHankel](../FD56/LinearAlgebra/StackedHankel.lean) and [BlockHankel](../FD56/LinearAlgebra/BlockHankel.lean) prove generic ranks by explicit permutation specializations. [GenericHankelFamily](../FD56/LinearAlgebra/GenericHankelFamily.lean) puts both rank statements over the same independent coefficient field.
- [HankelFrameMinimal](../FD56/Hilbert/HankelFrameMinimal.lean) proves that the inverse Hankel frame has the prescribed minimal kernel degrees. The proof constructs its kernel matrix, proves polynomial spanning and uniqueness over a polynomial coefficient ring, and verifies independent leading columns.
- [HankelBoundedImage](../FD56/Hilbert/HankelBoundedImage.lean) identifies every bounded frame image with its truncated Hankel relation space and constructs a polynomial right inverse. [HankelScalarObstruction](../FD56/Hilbert/HankelScalarObstruction.lean) turns scalar lifting into stacked Hankel equations.
- [GenericHankelScalar](../FD56/Hilbert/GenericHankelScalar.lean) proves a coefficient selector for the scalar kernel. [MixedOneHankelWitness](../FD56/Hilbert/MixedOneHankelWitness.lean) realizes the frame by an actual affine pair over a field extension. Specialization transfer and the existing lower bound prove the quotient-one SL formula over every base field.
- [RankSpecializationExtension](../FD56/LinearAlgebra/RankSpecializationExtension.lean) transfers rank bounds from arbitrary field specializations. [GenericKernelExtension](../FD56/Hilbert/GenericKernelExtension.lean) permits affine witnesses over field extensions without requiring a coefficient-ring section.
- [KroneckerSum](../FD56/Hilbert/KroneckerSum.lean), [BlockSum](../FD56/Hilbert/BlockSum.lean), and [ConstantEquivalence](../FD56/Hilbert/ConstantEquivalence.lean) prove bounded-kernel formulas for supplied blocks and invariance under supplied constant equivalences.

## Third-depth degree transfer

For 3m < n ≤ 4m, take reduced bases of the kernel of O₃ = (P, PM, PM²) and the transpose kernel of PM³V, where V is the first basis matrix. If their degrees are αᵢ and βⱼ, then the actual GL minimal degrees are all αᵢ + βⱼ + 3. Equivalently,

HGL(d) = ∑ᵢⱼ max(d + 1 − αᵢ − βⱼ − 3, 0).

[`generic_depth_three_gl_kernel_hilbert_of_bases`](../FD56/Hilbert/DepthThreeGL.lean) proves this for the universal affine pair over every base field. It discharges the right inverse, terminal injectivity, and leading-row conditions. [DepthThreeGLDegree](../FD56/Hilbert/DepthThreeGLDegree.lean) proves the column degree bounds; [DepthThreeGLLeading](../FD56/Hilbert/DepthThreeGLLeading.lean) proves independent leading columns of the explicit basis. Thus this is a statement about an actual reduced polynomial basis, not just a candidate Hilbert function.

The first list is already known: α = B(6m,n−3m). This transfer theorem does not determine β, so it does not yet give the complete third-depth generic classification.

The second auxiliary kernel now has a finite coefficient formulation. [ObservabilityBetaKernel](../FD56/Hilbert/ObservabilityBetaKernel.lean) identifies bounded relations with the actual auxiliary kernel at any depth, under explicit right-inverse and leading-row hypotheses. [ObservabilityBetaCoefficients](../FD56/Hilbert/ObservabilityBetaCoefficients.lean) constructs the finite coefficient matrix and proves the identification with its kernel. At depth three its domain has dimension m(4d+10), and its target has dimension n(d+5), giving the lower bound max(m(4d+10)−n(d+5),0).

[GenericObservabilityBetaTransfer](../FD56/Hilbert/GenericObservabilityBetaTransfer.lean) transfers upper bounds from actual affine pairs over field extensions to the universal pair. It also discharges the right-inverse and leading-row hypotheses for the actual third auxiliary kernel when 3m < n. A witness attaining the lower bound would therefore determine its bounded Hilbert function. No such general witness is constructed here: the relation blocks must arise from the same M and P, rather than independent matrices. This formulation does not establish the expected balanced second degree list.

[ObservabilityBetaGrowth](../FD56/Hilbert/ObservabilityBetaGrowth.lean) proves that the terminal auxiliary map remains injective at zero and bounds the left-kernel Hilbert function by s(d+1), with s equal to the number of rows minus the number of auxiliary columns. Together with the dimension lower bound, [DepthThreeBetaCriterion](../FD56/Hilbert/DepthThreeBetaCriterion.lean) reduces the third-depth balanced degree claim to two finite coefficient tests. Write r=n−3m, s=m−r, C=6m+4r, D=⌊C/s⌋, b=C mod s, and a=s−b. It suffices to show zero kernel at degree D−1 and kernel dimension at most a at degree D. The two tests may use different actual affine witnesses over a field extension. This is a proved sufficient criterion, not a construction of those witnesses.

[DepthThreeBetaSingleTest](../FD56/Hilbert/DepthThreeBetaSingleTest.lean) reduces the criterion to one test when s divides C. The Hilbert increment bound then supplies the second test automatically.

For n=7 and m=2 in characteristic zero, [DepthThreeSevenTwoData](../FD56/Hilbert/DepthThreeSevenTwoData.lean) gives an explicit affine pair, a polynomial vector annihilated by the third observability stack, and two terminal polynomials of degree 16 with a verified Bézout identity. [DepthThreeSevenTwoWitness](../FD56/Hilbert/DepthThreeSevenTwoWitness.lean) proves that their short relations vanish and that the stack rows are independent, establishing zero bounded auxiliary kernel at degree 15. [DepthThreeSevenTwo](../FD56/Hilbert/DepthThreeSevenTwo.lean) transfers this certificate to the generic pair: beta=[16], and the actual GL reduced kernel has the single degree 31. The certificate uses characteristic zero to invert its nonzero integer constant. This result does not cover all third-depth parameters or provide a formal canonical decomposition.

[ObservabilityBetaBlocks](../FD56/Hilbert/ObservabilityBetaBlocks.lean) proves that vanishing bounded auxiliary relations are preserved by diagonal block repetition. [DepthThreeSevenTwoFamily](../FD56/Hilbert/DepthThreeSevenTwoFamily.lean) applies the same certificate to every nonempty finite repetition index t: for n=7k, m=2k, k=card(t), the generic second list consists of k copies of 16, and the actual GL reduced kernel has k² degrees equal to 31. The formal theorem uses product index types Fin 7 × t and Fin 2 × t. No additional rank witness remains as a hypothesis in this characteristic-zero family.

[DepthThreeElevenThreeData](../FD56/Hilbert/DepthThreeElevenThreeData.lean) supplies an eleven-state, three-row affine pair with two explicit vectors annihilated by the third stack. The three maximal minors of their terminal images satisfy a verified Bézout identity, and one minor has degree 26. [IntegerPolynomial](../FD56/Hilbert/IntegerPolynomial.lean) proves the coefficient-list arithmetic used to check the explicit identities by kernel reduction. [DepthThreeElevenThreeWitness](../FD56/Hilbert/DepthThreeElevenThreeWitness.lean) uses these identities to exclude auxiliary relations of degree at most 25. [DepthThreeElevenThreeFamily](../FD56/Hilbert/DepthThreeElevenThreeFamily.lean) repeats this witness and transfers it to the generic pair: for n=11k and m=3k in characteristic zero, alpha has 2k copies of 9, beta has k copies of 26, and the actual GL reduced kernel has 2k² degrees equal to 38. The formal index types are Fin 11 × t and Fin 3 × t, with k=card(t)>0. No additional witness hypothesis remains.

## Remaining work

[GenericAffineDivisors](../FD56/LinearAlgebra/GenericAffineDivisors.lean) proves that a polynomial family with no common nonunit divisor retains this property after substitution along a generic affine line, over the fraction field of its independent intercept and slope coefficients. The proof constructs the substitution automorphism, adjoins independent variables, and descends primitive divisors through coefficient localization. It applies over every field. The required common-divisor statement for the static observability minors is not yet proved, so this transfer theorem does not add a classified GL or SL family.

[ObservabilityCovariance](../FD56/Stabilizer/ObservabilityCovariance.lean) proves that state-coordinate changes and invertible output changes preserve the common divisors of maximal observability minors. Their finite gcds are therefore associated. [MaximalMinorDivisors](../FD56/LinearAlgebra/MaximalMinorDivisors.lean) proves the underlying row-operation result by multilinear determinant expansion, and [FiniteGCDCovariance](../FD56/LinearAlgebra/FiniteGCDCovariance.lean) supplies gcd covariance under ring automorphisms. These statements do not establish that the gcd is a unit.

[ElementaryOutputSubstitution](../FD56/Stabilizer/ElementaryOutputSubstitution.lean) constructs the actual polynomial-parameter output substitution and proves that it fixes the universal minor gcd exactly. [StateCoefficientSubstitution](../FD56/Stabilizer/StateCoefficientSubstitution.lean) constructs invertible state substitutions and proves the corresponding association of gcds. [PolynomialGCDInvariance](../FD56/LinearAlgebra/PolynomialGCDInvariance.lean) supplies the parameter argument. These results still do not show that the gcd is a unit. For a separate transcendence-degree approach, [PolynomialHypersurface](../FD56/LinearAlgebra/PolynomialHypersurface.lean) proves coefficient-ring injectivity modulo a positive-degree relation, and [NonzeroMaximalMinor](../FD56/LinearAlgebra/NonzeroMaximalMinor.lean) extracts a nonsingular coordinate minor from independent columns.

The transcendence-degree route has several verified components. [KrylovSpan](../FD56/LinearAlgebra/KrylovSpan.lean) proves invariance of a dependent initial orbit. [FullKrylovGeneratorBound](../FD56/LinearAlgebra/FullKrylovGeneratorBound.lean) derives the reduced field generators and their bound on a nonsingular coordinate chart. [InvariantSubspaceCoordinates](../FD56/LinearAlgebra/InvariantSubspaceCoordinates.lean) proves the graph-coordinate block reduction. [NonconstantCoordinate](../FD56/LinearAlgebra/NonconstantCoordinate.lean), [HypersurfaceCoordinates](../FD56/LinearAlgebra/HypersurfaceCoordinates.lean), [QuotientFieldGenerators](../FD56/LinearAlgebra/QuotientFieldGenerators.lean), and [FiniteFieldGenerators](../FD56/LinearAlgebra/FiniteFieldGenerators.lean) establish the coordinate and field-generation tools. The two branches have not yet been combined into the static-minor coprimality theorem.

1. The second generic auxiliary list at block depth three and above; the first auxiliary list beyond the ranges proved above; and the resulting GL degree formula when n ≥ 3m outside the divisible families and the two characteristic-zero families above.
2. The SL Hilbert formula for n > 2m. The middle range m < n ≤ 2m is now covered over every field.
3. A formal canonical Jordan–Kronecker decomposition and identification of regular Jordan blocks. Zero polynomial kernel alone does not identify those blocks.
4. Rank-open loci and genericity on projective lines. The manuscript's Hirzebruch-surface argument and its use of the Coskun–Huizenga theorem are not formalized.

The arithmetic modules contain candidate formulas outside the proved cases. `glFormula` and `slFormula` are intended for positive n,m with 0 < n % m < m; their total Lean values elsewhere carry no classification assertion.

Every exported theorem is checked for dependencies, allowing only `propext`, `Classical.choice`, and `Quot.sound`. Passing the build certifies these Lean statements, not the full manuscript or its novelty.
