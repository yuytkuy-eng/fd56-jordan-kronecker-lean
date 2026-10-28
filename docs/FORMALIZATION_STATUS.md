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
| (n,m)=(10,4) | [13,13,13,14,14]: three blocks of dimension 27 and two of dimension 29 | Characteristic zero; [TenFourSLClassification](../FD56/Hilbert/TenFourSLClassification.lean) |

The two extreme-remainder families include every nondivisible three-output SL pencil in characteristic zero. The SL equations include their scalar term and use actual traceless coordinates; they are not replaced by the traceless part of the GL kernel.

SL lists need not be balanced. For (n,m)=(11k,8k), k≥1, the multiplicities at degrees 5,6,7 are k², 6k²+8, and 8k²−7. Thus (11,8) has one degree 5, fourteen degrees 6, and one degree 7. [MiddleSLClassification](../FD56/Hilbert/MiddleSLClassification.lean) proves the full list over every field; [HilbertObstruction](../FD56/Hilbert/HilbertObstruction.lean) supplies the corresponding obstruction to a balanced list. Balanced auxiliary lists in the GL proof do not imply balanced SL degrees.

## Proof of the general GL formula

For q≥1, put W=A+(q+1)r. The proof uses finite polynomial linear algebra throughout.

1. [GenericInteriorScalarFrame](../FD56/Hilbert/GenericInteriorScalarFrame.lean) constructs rs+1 independent scalar-gradient columns in the actual generic SL kernel. [GenericInteriorDifferentialRank](../FD56/Hilbert/GenericInteriorDifferentialRank.lean) uses the proved SL degree budget and affine dual lifting to bound the derivative image of selected observability minors below by mW+rs+1.
2. [InteriorSelectedMinorFactorization](../FD56/Stabilizer/InteriorSelectedMinorFactorization.lean) expresses those minors as Plücker coordinates of the actual terminal matrix, with one common nonzero constant factor. [ComplementaryKernelMinorReindex](../FD56/LinearAlgebra/ComplementaryKernelMinorReindex.lean) gives the dual factorization.
3. [WeightedPluckerDifferential](../FD56/LinearAlgebra/WeightedPluckerDifferential.lean) bounds the derivative rank using polynomial endomorphisms with prescribed degree bounds. [DegreeEndomorphismBudget](../FD56/Arithmetic/DegreeEndomorphismBudget.lean) shows that their dimension is at least the square of the number of columns, with equality exactly when the degrees differ by at most one. [PluckerDegreeBalance](../FD56/LinearAlgebra/PluckerDegreeBalance.lean) compares the upper and lower bounds.
4. [GenericInteriorDegreeBalance](../FD56/Hilbert/GenericInteriorDegreeBalance.lean) applies the comparison to both actual auxiliary bases. [GenericAllDepthGL](../FD56/Hilbert/GenericAllDepthGL.lean) then constructs the reduced GL basis and full Kronecker congruence; [GenericGLClassification](../FD56/Hilbert/GenericGLClassification.lean) identifies its degrees with `glFormula`.

The final GL theorems have no auxiliary-basis, witness, rank, or characteristic-zero assumptions. Their proof uses the previously established SL block count and total degree, without assuming the unresolved individual SL degrees.

## SL certificates and remaining work

[FourOutputInteriorSLTests](../FD56/Hilbert/FourOutputInteriorSLTests.lean) proves that two explicit bounded-kernel tests suffice for the balanced SL list B(8q²+16q+3,5) at (n,m)=(4q+2,4), q≥1. The tests remain hypotheses in the general theorem. The case q=1 is covered by the middle-range classification; q=2 is the characteristic-zero (10,4) theorem. The cases q≥3 remain unresolved.

[MonomialPluckerChart](../FD56/Hilbert/MonomialPluckerChart.lean) constructs, in characteristic zero and for W≥5, a six-coordinate polynomial row satisfying the Plücker relation, with two coprime coordinates, exact degree W, and kernel degrees B(W,5). This is a polynomial-row certificate. Its realization and transfer to the actual generic SL pencil remain unproved. [DerivationAlgebraicIndependence](../FD56/LinearAlgebra/DerivationAlgebraicIndependence.lean) supplies a characteristic-zero criterion for algebraic independence; it does not establish independence of all Plücker coefficients.

The main remaining classification work is the individual SL degrees at nondivisible n>2m outside the proved families, including positive-characteristic versions of the extreme-remainder formulas outside the ranges already covered. Block count, total degree, and pure Kronecker structure are proved there, but do not determine the missing degree lists. `slFormula` remains a candidate outside the established cases; `glFormula` is proved throughout its intended positive nondivisible domain.

## Parameter loci and verification

[GenericKroneckerLocus](../FD56/Hilbert/GenericKroneckerLocus.lean) transfers every proved pure Kronecker decomposition to a nonempty principal locus over an infinite base field. [GenericNondivisibleIndependentLocus](../FD56/Hilbert/GenericNondivisibleIndependentLocus.lean) puts the positive-depth nondivisible GL and SL decompositions on one such locus with independent ordered endpoints. [GenericDivisibleCanonicalLocus](../FD56/Stabilizer/GenericDivisibleCanonicalLocus.lean) gives the divisible GL/SL formulas for m≥2 on a nonempty principal locus over an algebraically closed infinite field. These statements do not assert a nonempty rational locus over finite fields. Descent to projective lines or a Grassmannian remains unformalized.

The inventory contains 785 modules and 3,185 exported theorems. The [checker](../scripts/check.py) builds the library and audits every export against `propext`, `Classical.choice`, and `Quot.sound`, rejecting placeholders and custom axioms. It checks the formal statements; manuscript claims and novelty require separate assessment.
