# Proof coverage

The generic GL classification is proved for every positive n,m. The SL classification is complete at positive divisible sizes and in the nondivisible ranges listed below; its general individual-degree formula remains open.

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
| n=12, m=5 | Seven copies of 14 | Characteristic zero; [GenericTwelveFiveSLTangentClassification](../FD56/Hilbert/GenericTwelveFiveSLTangentClassification.lean) |

The extreme-remainder families and the four-output interior theorem include every nondivisible SL pencil with at most four outputs in characteristic zero. The SL equations include their scalar term and use actual traceless coordinates; they are not replaced by the traceless part of the GL kernel.

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

[GenericTwoColumnPluckerSpecialization](../FD56/Hilbert/GenericTwoColumnPluckerSpecialization.lean) applies this to every n=(2+s)q+2, m=2+s, with s,q>0 in characteristic zero. Its final theorem has no basis, rank, or pivot premise: it constructs actual columns u,v with balanced degrees a,b, where 2(a+b)=(2+s)q(q+1)+4(q+1), realizes every selected generic observability minor as a minor of u,v, and proves that evaluation is injective on the full universal minor coefficient algebra. [GenericTwoColumnFullSpecialization](../FD56/Hilbert/GenericTwoColumnFullSpecialization.lean) extends the realization to every ordered-pair minor. This does not assert independence of all terminal coefficients. The tangent certificate below determines (12,5); the remaining larger-output SL lists still require further proof.

## SL certificates and remaining work

[GenericFourOutputSLClassification](../FD56/Hilbert/GenericFourOutputSLClassification.lean) proves the actual minimal list B(8q²+16q+3,5) and the full constant Kronecker congruence for (n,m)=(4q+2,4), every q≥1, in characteristic zero. Its final statements have no auxiliary-basis, witness, chart, or rank hypotheses. At q=2 this recovers [13,13,13,14,14]; at q=3 it gives [24,24,25,25,25]. The earlier bounded-kernel tests are no longer unresolved conditions for this family in characteristic zero.

The proof starts with the six actual augmented observability minors. [FourOutputGradientRowModule](../FD56/Hilbert/FourOutputGradientRowModule.lean) identifies their gradient row module exactly with the kernel of the polar Plücker row. [FourOutputSLDualDegrees](../FD56/Hilbert/FourOutputSLDualDegrees.lean) proves that its five minimal degrees are W−1−eᵢ, where W=2(q+1)² and eᵢ are the actual SL degrees. A [constant change over the base field](../FD56/Hilbert/GenericFourOutputCoprimeChart.lean) puts these minors in a full-degree coprime chart while preserving derivative rank. The resulting 4W+5 chart coordinates are algebraically independent in characteristic zero. [PluckerChartSpecialization](../FD56/Hilbert/PluckerChartSpecialization.lean) uses a finite linear system and determinant clearing to transfer the [balanced monomial certificate](../FD56/Hilbert/MonomialPluckerChart.lean) to that chart. Complementary degrees then give the SL list and full congruence. This argument does not assume independence of all Plücker coefficients or realization of the monomial witness as an affine pair.

For (n,m)=(12,5), [GenericTwelveFiveSLTangentClassification](../FD56/Hilbert/GenericTwelveFiveSLTangentClassification.lean) proves seven minimal degrees equal to 14 and a full constant congruence to seven Kronecker blocks of dimension 29, in characteristic zero. A kernel-checked [60-by-60 coefficient certificate](../FD56/Hilbert/FiveOutputTangentVanishing.lean) excludes nonzero tangent-kernel vectors of degree at most five. [Faithful specialization](../FD56/Hilbert/GenericTwelveFiveTangentVanishing.lean) transfers it to the actual generic minors. Their scalar gradients have degree at most 20; factoring them through a reduced SL kernel basis bounds each minimal degree by 14. The established seven-block degree sum 98 forces equality. This argument uses containment in the tangent kernel and does not require identifying the entire tangent module. The final theorem has no witness, rank, or vanishing premise.

For every positive nondivisible size, [GenericSLScalarHankel](../FD56/Hilbert/GenericSLScalarHankel.lean) identifies the bounded SL scalar image with the kernel of a signed Hankel obstruction. Its coefficients come from the actual trace covector under a constant GL Kronecker congruence. One choice of that covector and the proved GL degrees works for every degree d. Write eᵢ for these degrees, N for their number, and S for their sum.

Put G(d)=Σᵢ max(d+1−eᵢ,0) and Q(d)=Σᵢ max(eᵢ−d−1,0). The obstruction has d+2 columns and Q(d) rows. If R(d) is its rank, [GenericSLScalarEnvelope](../FD56/Hilbert/GenericSLScalarEnvelope.lean) proves, over every field,

```text
H_SL(d) + R(d) = G(d) + d + 2,
H_SL(d) >= max(G(d), (N+1)(d+1)+1-S).
```

Equality in the lower bound holds exactly when R(d)=min(d+2,Q(d)). The actual Hankel maximal-rank step remains unproved in general. A theorem for independent Hankel coefficients does not establish it. [GenericRingWitness](../FD56/Hilbert/GenericRingWitness.lean) provides integral specialization for future finite-field certificates, and [AffineEndpointCompression](../FD56/LinearAlgebra/AffineEndpointCompression.lean) reduces a bounded kernel test to an endpoint matrix. [TwelveFiveSLTests](../FD56/Hilbert/TwelveFiveSLTests.lean) retains its conditional degree-thirteen Hilbert-test criterion; the characteristic-zero case is now classified unconditionally by the tangent proof above.

The main remaining classification work is the individual SL degrees at nondivisible n>2m outside the proved families, including positive-characteristic versions of the extreme-remainder formulas outside the ranges already covered. Block count, total degree, and pure Kronecker structure are proved there, but do not determine the missing degree lists. `slFormula` remains a candidate outside the established cases; `glFormula` is proved throughout its intended positive nondivisible domain.

## Parameter loci and verification

[GenericKroneckerLocus](../FD56/Hilbert/GenericKroneckerLocus.lean) transfers every proved pure Kronecker decomposition to a nonempty principal locus over an infinite base field. [GenericNondivisibleIndependentLocus](../FD56/Hilbert/GenericNondivisibleIndependentLocus.lean) puts the positive-depth nondivisible GL and SL decompositions on one such locus with independent ordered endpoints. [GenericDivisibleCanonicalLocus](../FD56/Stabilizer/GenericDivisibleCanonicalLocus.lean) gives the divisible GL/SL formulas for m≥2 on a nonempty principal locus over an algebraically closed infinite field. These statements do not assert a nonempty rational locus over finite fields. Descent to projective lines or a Grassmannian remains unformalized.

The inventory contains 860 modules and 3,400 exported theorems. The [checker](../scripts/check.py) builds the library and audits every export against `propext`, `Classical.choice`, and `Quot.sound`, rejecting placeholders and custom axioms. It checks the formal statements; manuscript claims and novelty require separate assessment.
