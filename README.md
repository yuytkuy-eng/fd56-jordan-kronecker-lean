# Jordan–Kronecker invariants in Lean

[![Lean proofs](https://github.com/yuytkuy-eng/fd56-jordan-kronecker-lean/actions/workflows/lean.yml/badge.svg)](https://github.com/yuytkuy-eng/fd56-jordan-kronecker-lean/actions/workflows/lean.yml)

Lean formalization by Shifan Yu of Jordan–Kronecker invariants for general and special linear semidirect products.

The **generic GL classification is proved for every positive pair of sizes (n,m)**. For nondivisible sizes, [`generic_nondivisible_gl_formula`](FD56/Hilbert/GenericGLClassification.lean) gives the explicit minimal-degree list and a constant congruence of the whole pencil to its Kronecker blocks, over every base field. For divisible sizes, the library constructs the full Jordan decomposition after a coefficient-field extension.

The **generic SL classification is proved for every positive state dimension with at most six outputs in characteristic zero**. Existing wide, extreme-remainder and divisible results combine with the [five-output interior families](FD56/Hilbert/GenericFiveOutputInteriorSLClassification.lean), the [six-output remainders two and four](FD56/Hilbert/GenericSixOutputTwoColumnSLClassification.lean), and the [six-output middle remainder](FD56/Hilbert/GenericSixOutputMiddleSLClassification.lean). The nondivisible conclusions give explicit minimal-degree lists and full constant Kronecker congruences. At divisible sizes the Jordan congruence is constructed after an algebraically closed coefficient-field extension.

The **general SL classification remains incomplete**. For every positive nondivisible size, pure Kronecker structure, block count and total minimal degree are proved. Individual degrees are known over every field when m>n, when m<n<2m, and for odd n with m=2. Characteristic-zero results also cover every pencil with at most six outputs and the extreme remainders n≡±1 modulo m. Remaining work includes interior cases with m≥7, and positive-characteristic extensions outside the proved ranges. See [proof coverage](docs/FORMALIZATION_STATUS.md) for formulas and assumptions.

For every positive nondivisible size, the [actual SL scalar image](FD56/Hilbert/GenericSLScalarHankel.lean) is the kernel of a signed Hankel matrix formed from the trace covector in GL Kronecker coordinates. The [Hilbert lower bound is attained exactly when this matrix has maximal rank](FD56/Hilbert/GenericSLScalarEnvelope.lean). This reduction holds over every field; maximal rank remains unproved in general.

For every positive interior depth, the [actual derivative image of selected observability minors](FD56/Hilbert/GenericInteriorDifferentialImage.lean) equals the selected Plücker differential image of the terminal matrix with its column degree bounds. In characteristic zero, faithful specialization of the universal balanced two-column minor coefficient algebra holds for [remainder-two families](FD56/Hilbert/GenericTwoColumnPluckerSpecialization.lean) and [corank-two families through signed complementary minors](FD56/Hilbert/GenericCorankTwoPluckerSpecialization.lean). This transfers tangent coefficient certificates to the actual generic minors and determines the proved five-output SL lists from their total degree.

For five outputs, the weight classes not divisible by 14 use two tangent Hilbert bounds from [finite normalized seeds](FD56/Hilbert/FiveOutputBalancedSeeds.lean) and an [iterated splice](FD56/Hilbert/NormalizedFiveOutputIteration.lean). The divisible weight class uses a vanishing test and the total-degree budget. Faithful specialization transfers the bounds to the actual generic minors. The splice raises both column degree bounds by seven and shifts each tested kernel degree by four.

For six-output remainders two and four, the proof uses a [degree-three tail](FD56/Hilbert/PermutedSixOutputThreeTailWitness.lean) and a [short splice](FD56/Hilbert/NormalizedSixOutputShortSplice.lean) that raises both column bounds by three and shifts each kernel test by two. Two finite seeds handle weights not divisible by six; a power-substituted tail and the degree budget handle divisible weights.

For the six-output middle remainder n=6q+3, the actual minors faithfully evaluate a [three-column coefficient algebra](FD56/Hilbert/GenericSixOutputTripleSpecialization.lean). A degree-five tail and two normalized finite seeds supply the tangent Hilbert bounds. The recurrence raises all three column bounds by five and shifts each kernel test by six. The resulting list has ten balanced degrees with sum 18(q+1)²−10.

Here generic means the universal affine pair over the rational function field of its independent coefficients. The GL proof compares the [differential rank of selected observability minors](FD56/Hilbert/GenericInteriorDifferentialRank.lean) with a [degree-dependent Plücker rank bound](FD56/LinearAlgebra/PluckerDegreeBalance.lean). This forces both [actual auxiliary degree lists to be balanced](FD56/Hilbert/GenericInteriorDegreeBalance.lean); [GenericAllDepthGL](FD56/Hilbert/GenericAllDepthGL.lean) reconstructs the reduced kernel basis and full constant congruence. For four-output SL, an [explicit balanced Plücker certificate](FD56/Hilbert/MonomialPluckerChart.lean) now transfers to the actual generic family through [coprime chart specialization](FD56/Hilbert/PluckerChartSpecialization.lean) and [complementary minimal degrees](FD56/Hilbert/FourOutputSLDualDegrees.lean).

## Check the proofs

Install [elan](https://github.com/leanprover/elan), Git, and Python 3. From this repository, run:

```sh
lake exe cache get
python scripts/check.py
```

The library contains 1302 Lean modules and 4,129 exported theorems. The checker builds every module and audits every exported theorem, allowing only `propext`, `Classical.choice`, and `Quot.sound`. It validates each batch and the complete inventory, rejects missing output or failed processes, and rejects placeholder proofs, custom axioms, and `native_decide`. Temporary audit files stay in `.verification/`. GitHub Actions runs the same check.

The toolchain and dependency files pin Lean and mathlib. For a build without the audit, run `lake build`. To use the library, write `import FD56`.

## Source layout

| Directory | Content |
| --- | --- |
| [LinearAlgebra](FD56/LinearAlgebra/) | Polynomial kernels, degree reduction, Plücker differentials, and hyperplane radicals |
| [Stabilizer](FD56/Stabilizer/) | GL/SL equations, observability matrices, and canonical congruences |
| [Hilbert](FD56/Hilbert/) | Minimal degrees, generic classifications, and SL certificates |
| [Arithmetic](FD56/Arithmetic/) | Explicit spectra, degree budgets, and Hilbert identities |

The public theorem namespace is `FD56`.

## License

Copyright 2026 Shifan Yu. Original source code, scripts, and documentation in this repository are licensed under [Apache-2.0](LICENSE). See [NOTICE](NOTICE). External dependencies retain their own licenses. This repository does not distribute the manuscript.
