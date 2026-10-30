# Proof coverage

The generic GL classification is proved for every positive n,m. In characteristic zero, the generic SL classification is also proved for every positive n with 1≤m≤6. At positive divisible sizes, the Jordan congruence is constructed after an algebraically closed coefficient-field extension. The general SL individual-degree formula remains open outside the ranges below.

Here n is the state dimension, m is the number of rows of P, and **generic** means the universal affine pair over the rational function field of its independent coefficients. Results hold over every base field unless stated otherwise. A minimal degree e gives a Kronecker block of dimension 2e+1. Write B(D,R) for the balanced list of R nonnegative integers with sum D.

## GL at every nondivisible size

Let n=qm+r, with q≥0, 0<r<m, and s=m−r. Set

A=mq(q+1)/2, B=A+(q+1)r, α=B(A,r), β=B(B,s).

The actual GL minimal degrees are all αᵢ+βⱼ+q. The whole pencil consists of these rs Kronecker blocks. This includes n<m and every positive depth, in every characteristic.

Equivalently, put a=⌊A/r⌋, u=A mod r, b=⌊B/s⌋, v=B mod s, and E=a+b+q. The list has at most three adjacent degrees:

| Degree | Multiplicity |
| --- | --- |
| E | (r−u)(s−v) |
| E+1 | u(s−v)+(r−u)v |
| E+2 | uv |

[`generic_nondivisible_gl_formula`](../FD56/Hilbert/GenericGLClassification.lean) proves both `HasMinimalKernelDegrees` and `HasKroneckerDecomposition` for `glFormula n m`, with only m>0 and n mod m≠0 as size assumptions. [GLBalancedFormula](../FD56/Hilbert/GLBalancedFormula.lean) identifies the balanced convolution with the table. Earlier GL certificates remain valid, but their depth and characteristic restrictions do not restrict this general theorem.

`HasMinimalKernelDegrees` contains an actual polynomial kernel basis with independent leading columns. `HasKroneckerDecomposition` contains mutually inverse constant matrices giving a congruence of the entire Kirillov pencil to the stated blocks.

## Positive divisible sizes

Let n=qm, q≥1, m≥1, and D=mq(q+1)/2. After an algebraically closed coefficient-field extension, the block lists are:

| Case | Canonical blocks |
| --- | --- |
| GL, m≥2 | D distinct poles, each with one Jordan block of dimension 4 and m−2 blocks of dimension 2 |
| GL, m=1 | D distinct poles, each with one Jordan block of dimension 2 |
| SL, m≥2 | One Kronecker block of dimension 2D−1, and m−1 Jordan blocks of dimension 2 at each of the D poles |
| SL, m=1 | One Kronecker block of dimension 2D−1 |

The full constant congruences and their inverses are constructed in [GenericDivisibleGLJordan](../FD56/Stabilizer/GenericDivisibleGLJordan.lean), [GenericDivisibleSLJordan](../FD56/Stabilizer/GenericDivisibleSLJordan.lean), [OneOutputGL](../FD56/Hilbert/OneOutputGL.lean), and [OneOutputSL](../FD56/Hilbert/OneOutputSL.lean). The unique SL minimal degree D−1 is already proved over the original generic coefficient field in [GenericDivisibleSLDegrees](../FD56/Stabilizer/GenericDivisibleSLDegrees.lean). These statements cover square sizes as q=1.

## Nondivisible SL coverage

For every positive nondivisible size, the generic SL pencil is purely Kronecker over the original generic coefficient field. With r=n mod m and s=m−r, it has rs+1 blocks and total minimal degree (n(n+m)−rs)/2−1. [GenericNondivisibleSLStructure](../FD56/Hilbert/GenericNondivisibleSLStructure.lean) proves the positive-depth result; [MixedSLKronecker](../FD56/Hilbert/MixedSLKronecker.lean) covers n<m. The individual degrees are determined in the following ranges.

| Parameters | SL minimal degrees or multiplicities | Assumptions and source |
| --- | --- | --- |
| m>n>0 | B(n²−1,n(m−n)+1) | Every field; [GenericMinimal](../FD56/Hilbert/GenericMinimal.lean) |
| m<n<2m | Complete Hilbert function and every degree multiplicity | Every field; [MiddleSLClassification](../FD56/Hilbert/MiddleSLClassification.lean), [MixedOneSLHilbert](../FD56/Hilbert/MixedOneSLHilbert.lean), [MixedOneSLClassification](../FD56/Hilbert/MixedOneSLClassification.lean) |
| n=2q+1, m=2, q≥0 | Two copies of q(q+2) | Every field; [TwoOutputOddSL](../FD56/Hilbert/TwoOutputOddSL.lean) |
| n=mq+1, m≥2, q≥0 | m copies of (mq²+(m+2)q)/2 | Characteristic zero; [ResidueOneSL](../FD56/Hilbert/ResidueOneSL.lean) |
| n=mq+m−1, m≥2, q≥0 | m copies of (mq²+(3m−2)q+2m−4)/2 | Characteristic zero; [TerminalCorankOneSL](../FD56/Hilbert/TerminalCorankOneSL.lean) |
| n=4q+2, m=4, q≥1 | B(8q²+16q+3,5) | Characteristic zero; [GenericFourOutputSLClassification](../FD56/Hilbert/GenericFourOutputSLClassification.lean) |
| n=5q+2, m=5, q≥1 | B(5W−7,7), W=(5q²+9q+4)/2 | Characteristic zero; [GenericFiveOutputInteriorSLClassification](../FD56/Hilbert/GenericFiveOutputInteriorSLClassification.lean) |
| n=5q+3, m=5, q≥1 | B(5W−7,7), W=(5q²+11q+6)/2 | Characteristic zero; [GenericFiveOutputInteriorSLClassification](../FD56/Hilbert/GenericFiveOutputInteriorSLClassification.lean) |
| n=6q+2, m=6, q≥1 | B(6W−9,9), W=3q²+5q+2 | Characteristic zero; [GenericSixOutputTwoColumnSLClassification](../FD56/Hilbert/GenericSixOutputTwoColumnSLClassification.lean) |
| n=6q+3, m=6, q≥1 | B(6W−10,10), W=3(q+1)² | Characteristic zero; [GenericSixOutputMiddleSLClassification](../FD56/Hilbert/GenericSixOutputMiddleSLClassification.lean) |
| n=6q+4, m=6, q≥1 | B(6W−9,9), W=3q²+7q+4 | Characteristic zero; [GenericSixOutputTwoColumnSLClassification](../FD56/Hilbert/GenericSixOutputTwoColumnSLClassification.lean) |

Together with the wide and extreme-remainder results, the interior theorems for four, five and six outputs cover every positive nondivisible SL pencil with at most six outputs in characteristic zero. The SL equations include their scalar term and use actual traceless coordinates; they are not replaced by the traceless part of the GL kernel.

SL lists need not be balanced. For (n,m)=(11k,8k), k≥1, the multiplicities at degrees 5,6,7 are k², 6k²+8, and 8k²−7. Thus (11,8) has one degree 5, fourteen degrees 6, and one degree 7. [MiddleSLClassification](../FD56/Hilbert/MiddleSLClassification.lean) proves the full list over every field; [HilbertObstruction](../FD56/Hilbert/HilbertObstruction.lean) supplies the corresponding obstruction to a balanced list. Balanced auxiliary lists in the GL proof do not imply balanced SL degrees.

## Proof of the general GL formula

For q≥1, put W=A+(q+1)r. The proof uses finite polynomial linear algebra throughout.

1. [GenericInteriorScalarFrame](../FD56/Hilbert/GenericInteriorScalarFrame.lean) constructs rs+1 independent scalar-gradient columns in the actual generic SL kernel. [GenericInteriorDifferentialRank](../FD56/Hilbert/GenericInteriorDifferentialRank.lean) uses the proved SL degree budget and affine dual lifting to bound the derivative image of selected observability minors below by mW+rs+1.
2. [InteriorSelectedMinorFactorization](../FD56/Stabilizer/InteriorSelectedMinorFactorization.lean) expresses those minors as Plücker coordinates of the actual terminal matrix, with one common nonzero constant factor. [ComplementaryKernelMinorReindex](../FD56/LinearAlgebra/ComplementaryKernelMinorReindex.lean) gives the dual factorization.
3. [WeightedPluckerDifferential](../FD56/LinearAlgebra/WeightedPluckerDifferential.lean) bounds the derivative rank using polynomial endomorphisms with prescribed degree bounds. [DegreeEndomorphismBudget](../FD56/Arithmetic/DegreeEndomorphismBudget.lean) shows that their dimension is at least the square of the number of columns, with equality exactly when the degrees differ by at most one. [PluckerDegreeBalance](../FD56/LinearAlgebra/PluckerDegreeBalance.lean) compares the upper and lower bounds.
4. [GenericInteriorDegreeBalance](../FD56/Hilbert/GenericInteriorDegreeBalance.lean) applies the comparison to both actual auxiliary bases. [GenericAllDepthGL](../FD56/Hilbert/GenericAllDepthGL.lean) then constructs the reduced GL basis and full Kronecker congruence; [GenericGLClassification](../FD56/Hilbert/GenericGLClassification.lean) identifies its degrees with `glFormula`.

The final GL theorems have no auxiliary-basis, witness, rank, or characteristic-zero assumptions. Their proof uses the previously established SL block count and total degree, without assuming the unresolved individual SL degrees.

[GenericInteriorDifferentialImage](../FD56/Hilbert/GenericInteriorDifferentialImage.lean) also proves that the actual derivative image of the selected observability minors equals the selected Plücker differential image of the terminal matrix, allowing all entry variations within its column degree bounds and variation of the common scalar factor. This holds over every field at every positive interior depth, for any reduced observability kernel basis. The proof combines containment with the sharp dimension bounds; it does not assume independent terminal coefficients.

[PolynomialDerivationCoordinates](../FD56/LinearAlgebra/PolynomialDerivationCoordinates.lean) identifies this polynomial differential rank with the rank of its finite coefficient family. [DerivationIndependentSubfamily](../FD56/LinearAlgebra/DerivationIndependentSubfamily.lean) selects an algebraically independent subfamily in characteristic zero. Together they prove injectivity of a specialization from a domain when its transcendence degree is at most the actual differential rank.

For two columns of degrees a,b with b=a or a+1, [TwoColumnPluckerTranscendence](../FD56/LinearAlgebra/TwoColumnPluckerTranscendence.lean) proves that the universal minor coefficient algebra has transcendence degree at most m(a+b+2)−3 over every field. Four normalized coefficient slots and one retained scalar give the bound. This algebra lies in the original polynomial coefficient ring. [TwoColumnPluckerDominance](../FD56/LinearAlgebra/TwoColumnPluckerDominance.lean) combines the bound with actual differential rank to prove faithful coefficient evaluation in characteristic zero, without evaluating arbitrary rational denominators.

[GenericTwoColumnPluckerSpecialization](../FD56/Hilbert/GenericTwoColumnPluckerSpecialization.lean) applies this to every n=(2+s)q+2, m=2+s, with s,q>0 in characteristic zero. Its final theorem has no basis, rank, or pivot premise: it constructs actual columns u,v with balanced degrees a,b, where 2(a+b)=(2+s)q(q+1)+4(q+1), realizes every selected generic observability minor as a minor of u,v, and proves that evaluation is injective on the full universal minor coefficient algebra. [GenericTwoColumnFullSpecialization](../FD56/Hilbert/GenericTwoColumnFullSpecialization.lean) extends the realization to every ordered-pair minor. This does not assert independence of all terminal coefficients. The tangent certificates and splice below determine both five-output interior families at every positive depth; larger-output SL lists still require further proof.

## SL certificates and remaining work

[GenericFourOutputSLClassification](../FD56/Hilbert/GenericFourOutputSLClassification.lean) proves the actual minimal list B(8q²+16q+3,5) and the full constant Kronecker congruence for (n,m)=(4q+2,4), every q≥1, in characteristic zero. Its final statements have no auxiliary-basis, witness, chart, or rank hypotheses. At q=2 this recovers [13,13,13,14,14]; at q=3 it gives [24,24,25,25,25]. The earlier bounded-kernel tests are no longer unresolved conditions for this family in characteristic zero.

The proof starts with the six actual augmented observability minors. [FourOutputGradientRowModule](../FD56/Hilbert/FourOutputGradientRowModule.lean) identifies their gradient row module exactly with the kernel of the polar Plücker row. [FourOutputSLDualDegrees](../FD56/Hilbert/FourOutputSLDualDegrees.lean) proves that its five minimal degrees are W−1−eᵢ, where W=2(q+1)² and eᵢ are the actual SL degrees. A [constant change over the base field](../FD56/Hilbert/GenericFourOutputCoprimeChart.lean) puts these minors in a full-degree coprime chart while preserving derivative rank. The resulting 4W+5 chart coordinates are algebraically independent in characteristic zero. [PluckerChartSpecialization](../FD56/Hilbert/PluckerChartSpecialization.lean) uses a finite linear system and determinant clearing to transfer the [balanced monomial certificate](../FD56/Hilbert/MonomialPluckerChart.lean) to that chart. Complementary degrees then give the SL list and full congruence. This argument does not assume independence of all Plücker coefficients or realization of the monomial witness as an affine pair.

[GenericFiveOutputInteriorSLClassification](../FD56/Hilbert/GenericFiveOutputInteriorSLClassification.lean) proves the balanced list B(5W−7,7) and full constant Kronecker congruence for both n=5q+2 and n=5q+3, m=5, every q≥1, in characteristic zero. Here W is the corresponding weight in the table above. The final statements hold in every trace chart and have no witness, rank or vanishing premise. For example, (12,5) has seven degrees 14; (13,5) has six degrees 16 and one degree 17; (18,5) has seven degrees 29.

The proof uses the actual scalar gradients, whose degree is at most W−1. They factor through a reduced SL kernel basis and satisfy the five Plücker tangent equations. [Faithful two-column specialization](../FD56/Hilbert/GenericTwoColumnFullSpecialization.lean) handles remainder two; [signed complementary minors](../FD56/Hilbert/GenericCorankTwoPluckerSpecialization.lean) handle remainder three. For W not divisible by 14, write H for bounded tangent-kernel dimension and k=⌊2W/7⌋. The tests H(k−1)=0 and H(k)≤7−(2W mod 7), together with the seven-block total degree, determine the balanced SL list. When W is divisible by 14, a vanishing test and the total-degree budget already force the uniform list. Containment in the tangent kernel suffices; the proof does not assume equality with the entire tangent module.

For q≥2, [the weight arithmetic](../FD56/Arithmetic/FiveOutputSeedWeights.lean) writes W=s+14t with s in {14,16,17,18,21,23,24,25}. The weight-14 branch uses the existing power-substituted degree-seven witness. The [other seven normalized seeds](../FD56/Hilbert/FiveOutputBalancedSeeds.lean) have balanced column degrees summing to s. Exact integral coefficient minors, checked in the Lean kernel and transferred from a finite field to characteristic zero, prove the two required Hilbert bounds for each seed.

[NormalizedFiveOutputSplice](../FD56/Hilbert/NormalizedFiveOutputSplice.lean) preserves the constant columns (1,0,0,0,0) and (0,−1,0,0,0), raises both column degree bounds by seven, and gives H_new(d+4)≤H_old(d) for all d≥0 over a parameter fraction field. Its certified tail forces X⁴ divisibility under diagonal rescaling; multiplication by the nonzero coefficient scalar ε⁻⁷ restores the constants without changing kernels. [Iteration](../FD56/Hilbert/NormalizedFiveOutputIteration.lean) shifts both critical tests by 4t. [Extension-field transfer](../FD56/Hilbert/FiveOutputIteratedSeedTransfer.lean) then applies them to the actual generic family. The two q=1 cases use [previous first-depth classifications](../FD56/Hilbert/GenericFiveOutputSLBalancedBaseCases.lean).

[GenericSixOutputTwoColumnSLClassification](../FD56/Hilbert/GenericSixOutputTwoColumnSLClassification.lean) proves the balanced list B(6W−9,9) and full constant Kronecker congruence for n=6q+2 and n=6q+4, m=6, every q≥1, in characteristic zero. The final statements hold in every trace chart and have no witness or rank premises. In particular, (14,6) has nine degrees 15 and (16,6) has nine degrees 19.

The actual scalar-gradient factor has nine rows, entry degree bound W−1, and total minimal degree 6W−9. Faithful two-column minor specialization transfers tangent Hilbert bounds from bounded witnesses. At weights not divisible by six, the required tests are H(k−1)=0 and H(k)≤9−(3W mod 9), with k=⌊W/3⌋ and H the bounded kernel dimension of the fifteen Plücker tangent equations.

A [kernel-checked cubic tail](../FD56/Hilbert/PermutedSixOutputThreeTailWitness.lean) has no tangent-kernel vector of degree at most one. Its constant columns are e₂,−e₃ and its leading columns are e₀,−e₁. The [short normalized splice](../FD56/Hilbert/NormalizedSixOutputShortSplice.lean) restores the prescribed constants using a nonzero parameter scalar and the fixed row permutation (0 2)(1 3), whose effect on tangent kernels is proved. Each step raises the two column bounds by three and shifts the kernel degree by two. The [weight reduction](../FD56/Arithmetic/SixOutputSeedWeights.lean) and [two finite seeds](../FD56/Hilbert/SixOutputBalancedSeeds.lean) cover the nondivisible weight classes. For W=6h, [power substitution](../FD56/Hilbert/GenericSixOutputSLDivisibleTangent.lean) gives vanishing through degree 2h−1; the degree budget forces nine equal SL degrees 4h−1. No unproved maximal-rank premise is used in these final classifications.

[GenericSixOutputMiddleSLClassification](../FD56/Hilbert/GenericSixOutputMiddleSLClassification.lean) completes the middle remainder n=6q+3 for every q≥1 in characteristic zero. With W=3(q+1)², its ten minimal degrees form B(6W−10,10), and it constructs a full constant Kronecker congruence in every trace chart. For example, (15,6) has eight degrees 15 and two degrees 16; (27,6) has ten degrees 44. No auxiliary rank or witness premise remains.

The proof realizes all actual triple minors by a three-column frame with common degree bound h=(q+1)². Normalizing nine leading coefficients and retaining one scalar bounds the universal minor coefficient algebra's transcendence degree by 18h+10. The matching actual differential lower bound proves faithful specialization. Twenty original Plücker equations, closed under the endpoint row permutation, annihilate the actual gradients. Equality with the full Grassmannian tangent module is not required.

A [degree-five tail](../FD56/Hilbert/SixOutputThreeColumnTailWitness.lean) has no bounded tangent-kernel vector through degree five. Its [normalized iteration](../FD56/Hilbert/NormalizedSixOutputTripleIteration.lean) gives H_new(d+6t)≤H_seed(d) while raising each column bound by 5t. The square degree h has residues 0, 1 or 4 modulo five. The [two finite seeds](../FD56/Hilbert/SixOutputTripleBalancedSeeds.lean) of column degrees one and four handle the latter classes. If h=5t, [power substitution and the total-degree budget](../FD56/Hilbert/GenericSixOutputTripleSLDivisibleTangent.lean) force ten equal degrees 9t−1.

For every positive nondivisible size, [GenericSLScalarHankel](../FD56/Hilbert/GenericSLScalarHankel.lean) identifies the bounded SL scalar image with the kernel of a signed Hankel obstruction. Its coefficients come from the actual trace covector under a constant GL Kronecker congruence. One choice of that covector and the proved GL degrees works for every degree d. Write eᵢ for these degrees, N for their number, and S for their sum.

Put G(d)=Σᵢ max(d+1−eᵢ,0) and Q(d)=Σᵢ max(eᵢ−d−1,0). The obstruction has d+2 columns and Q(d) rows. If R(d) is its rank, [GenericSLScalarEnvelope](../FD56/Hilbert/GenericSLScalarEnvelope.lean) proves, over every field,

```text
H_SL(d) + R(d) = G(d) + d + 2,
H_SL(d) >= max(G(d), (N+1)(d+1)+1-S).
```

Equality in the lower bound holds exactly when R(d)=min(d+2,Q(d)). The actual Hankel maximal-rank step remains unproved in general. A theorem for independent Hankel coefficients does not establish it. [GenericRingWitness](../FD56/Hilbert/GenericRingWitness.lean) provides integral specialization for future finite-field certificates, and [AffineEndpointCompression](../FD56/LinearAlgebra/AffineEndpointCompression.lean) reduces a bounded kernel test to an endpoint matrix. [TwelveFiveSLTests](../FD56/Hilbert/TwelveFiveSLTests.lean) retains its conditional degree-thirteen Hilbert-test criterion; the characteristic-zero case is now classified unconditionally by the tangent proof above.

The main remaining classification work is the individual SL degrees for interior cases with m≥7 outside the proved ranges, together with positive-characteristic extensions of the characteristic-zero results. Block count, total degree, and pure Kronecker structure are proved there, but do not determine the missing degree lists. `slFormula` remains a candidate outside the established cases; `glFormula` is proved throughout its intended positive nondivisible domain.

## Parameter loci and verification

[GenericKroneckerLocus](../FD56/Hilbert/GenericKroneckerLocus.lean) transfers every proved pure Kronecker decomposition to a nonempty principal locus over an infinite base field. [GenericNondivisibleIndependentLocus](../FD56/Hilbert/GenericNondivisibleIndependentLocus.lean) puts the positive-depth nondivisible GL and SL decompositions on one such locus with independent ordered endpoints. [GenericDivisibleCanonicalLocus](../FD56/Stabilizer/GenericDivisibleCanonicalLocus.lean) gives the divisible GL/SL formulas for m≥2 on a nonempty principal locus over an algebraically closed infinite field. These statements do not assert a nonempty rational locus over finite fields. Descent to projective lines or a Grassmannian remains unformalized.

The inventory contains 1302 modules and 4,129 exported theorems. The [checker](../scripts/check.py) builds the library and audits every export against `propext`, `Classical.choice`, and `Quot.sound`, rejecting placeholders and custom axioms. It checks the formal statements; manuscript claims and novelty require separate assessment.
