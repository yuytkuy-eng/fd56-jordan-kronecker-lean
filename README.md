# Jordan–Kronecker invariants in Lean

[![Lean proofs](https://github.com/yuytkuy-eng/fd56-jordan-kronecker-lean/actions/workflows/lean.yml/badge.svg)](https://github.com/yuytkuy-eng/fd56-jordan-kronecker-lean/actions/workflows/lean.yml)

Partial Lean formalization by Shifan Yu, concerning general and special linear semidirect products.

The library determines actual reduced polynomial kernel-basis degrees for GL and SL when m ≥ n (SL: n > 0), every GL list with m < n < 3m, and every SL degree multiplicity with m < n ≤ 2m. The GL polynomial kernel vanishes whenever n is a positive multiple of m. These results hold over every field.

At depth three, all sizes (n,m)=((4a−1)k,ak), a≥2 and k≥1, are covered over every field. Characteristic-zero results also cover (10k,3k), (13k,4k), (16k,5k), (17k,5k), (18k,5k), and (19k,6k). The last family has 5k² degrees equal to 47 and 5k² Kronecker blocks of dimension 95. **The complete generic GL/SL classification is not formalized.** See [proof coverage](docs/FORMALIZATION_STATUS.md) for formulas, assumptions, and remaining work.

At arbitrary depth, the family (n,m)=((2q+1)k,2k), q≥0 and k>0, is classified over every field: the whole GL pencil consists of k² Kronecker blocks of dimension 4q²+8q+3.

At depth four, the characteristic-zero family (14k,3k), k>0, has 2k² GL minimal degrees equal to 59 and a full decomposition into 2k² Kronecker blocks of dimension 119.

All the nondivisible GL ranges above now have actual constant congruences of the full Kirillov pencil to standard Kronecker blocks: m>n, m<n<3m with n≠2m, and the proved families at depths three and four. A general theorem constructs this decomposition from any actual minimal-degree list and the full dimension equality, including characteristic two. The change of coordinates is constant in the pencil variable, over the rational function field of the generic coefficients.

The same canonical conclusion holds for SL when m>n>0, when m<n<2m, and for every (n,m)=(2q+1,2), q≥0. The odd-state family has two minimal degrees q(q+2) and two Kronecker blocks of dimension 2q(q+2)+1, over every field. The case (5,2) is the corollary [8,8], with two 17-dimensional blocks. The actual SL matrix uses traceless coordinates, with a proved equivalence to the full SL equations.

In characteristic zero, the SL pair (10,3) has three Kronecker blocks of dimension 43, with degrees [21,21,21]; the pair (14,3) has three blocks of dimension 79, with degrees [39,39,39]. These are full constant congruences in every trace chart.

For positive n,m, a general theorem transfers every proved pure generic GL decomposition to pure SL structure: the number of blocks increases by one and the total minimal degree decreases by one. For the repeated families (10k,3k) and (14k,3k), the exact individual SL degrees for k>1 remain unspecified.

Every one-output pencil (n,m)=(N,1), N≥1, is now classified over every field. The SL pencil is one Kronecker block of dimension N(N+1)−1, with minimal degree N(N+1)/2−1. After a coefficient-field extension, the GL pencil has N(N+1)/2 distinct poles and one Jordan block of dimension 2 at each pole, with a proved constant congruence and its inverse.

Every proved generic pure Kronecker decomposition persists on a nonempty principal parameter locus over an infinite base field.

The generic GL and SL pencils at every positive divisible size n=qm, q≥1, are fully classified over every base field, after an algebraically closed coefficient extension. Put D=mq(q+1)/2. For m≥2, the GL pencil has D distinct poles, each with one Jordan block of dimension 4 and m−2 blocks of dimension 2. The SL pencil has one Kronecker block of dimension 2D−1 and m−1 Jordan blocks of dimension 2 at each pole. Both proofs construct mutually inverse constant matrices giving the full canonical congruence.

The unique SL minimal degree is D−1 over the original generic coefficient field, for every m>0. Its leading matrix has nullity one. For m≥2, its nullity at a finite pole is 2m−1 and is one elsewhere.

Over an algebraically closed infinite field, these divisible GL/SL block formulas for m≥2 hold at every point of a nonempty principal locus in the original space of ordered affine pairs. The two matrix-pair endpoints are linearly independent there. Descent to a Grassmannian of projective lines remains open.

At every positive depth q with qm<n≤(q+1)m, the GL kernel has a proved reduced basis with degrees αᵢ+βⱼ+q, given the two actual auxiliary degree profiles. The polynomial right inverse and every generic rank and leading-coefficient condition are proved. The missing higher-depth profiles remain explicit inputs.

For every depth q, the maximal minors of the universal observability matrix (P, PM, ..., PM^(q−1)) have only unit common divisors when m ≥ 2 and n < qm. The same theorem holds for the generic affine pair over every base field. Cofactors determine the corank-one third-depth family and the exact bounded auxiliary relation dimensions in every corank-one depth. Other higher-depth degree lists remain open.

The corresponding universal and generic affine minor-coprimality theorems are also proved for every strictly wide stack qm<n, over every field, together with an actual polynomial right inverse. The proof combines separability and diagonalization with cyclic determinant identities and coefficient-field descent.

## Check the proofs

Install [elan](https://github.com/leanprover/elan), Git, and Python 3. From this repository, run:

```sh
lake exe cache get
python scripts/check.py
```

The verified inventory contains 691 Lean modules and 2,902 exported theorems. The toolchain and dependency files pin Lean and mathlib. The check builds every module and audits every theorem for axiom dependencies, allowing only `propext`, `Classical.choice`, and `Quot.sound`. Checks run in batches of at most 100 theorems, with both each batch and the complete inventory validated. Missing output or a failed process fails the audit. It rejects placeholder proofs, custom axioms, and `native_decide`. Temporary audit files go in `.verification/` and are not committed. GitHub Actions runs the same check.

For a build without the audit, run `lake build`. To use the library, write `import FD56`.

## Source layout

| Directory | Content |
| --- | --- |
| [LinearAlgebra](FD56/LinearAlgebra/) | Polynomial kernel bases, degree reduction, and hyperplane radicals |
| [Stabilizer](FD56/Stabilizer/) | Kernel constructions, block reduction, radical dimensions, full SL equations |
| [Hilbert](FD56/Hilbert/) | Kernel dimensions, minimal degrees, SL profiles, and balancing obstruction |
| [Arithmetic](FD56/Arithmetic/) | Candidate spectrum and numerical Hilbert identities |

The public theorem namespace remains `FD56`. Module imports now follow the directories above.

## License

Copyright 2026 Shifan Yu. Original source code, scripts, and documentation in this repository are licensed under [Apache-2.0](LICENSE). See [NOTICE](NOTICE). External dependencies retain their own licenses. This repository does not distribute the manuscript.
