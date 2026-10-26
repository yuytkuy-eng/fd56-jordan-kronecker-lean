# Jordan–Kronecker invariants in Lean

[![Lean proofs](https://github.com/yuytkuy-eng/fd56-jordan-kronecker-lean/actions/workflows/lean.yml/badge.svg)](https://github.com/yuytkuy-eng/fd56-jordan-kronecker-lean/actions/workflows/lean.yml)

Partial Lean formalization by Shifan Yu, concerning general and special linear semidirect products.

The library determines actual reduced polynomial kernel-basis degrees for GL and SL when m ≥ n (SL: n > 0), every GL list with m < n < 3m, and every SL degree multiplicity with m < n ≤ 2m. The GL polynomial kernel vanishes whenever n is a positive multiple of m. These results hold over every field.

At depth three, all sizes (n,m)=((4a−1)k,ak), a≥2 and k≥1, are covered over every field. Characteristic-zero results also cover (10k,3k), (13k,4k), and (16k,5k); the last family has 2k² degrees equal to 41 and 2k² equal to 42. **The complete generic GL/SL classification is not formalized.** See [proof coverage](docs/FORMALIZATION_STATUS.md) for formulas, assumptions, and remaining work.

At arbitrary depth, the family (n,m)=((2q+1)k,2k), q≥0 and k>0, is classified over every field: the whole GL pencil consists of k² Kronecker blocks of dimension 4q²+8q+3.

All the nondivisible GL ranges above now have actual constant congruences of the full Kirillov pencil to standard Kronecker blocks: m>n, m<n<3m with n≠2m, and the proved third-depth families. A general theorem constructs this decomposition from any actual minimal-degree list and the full dimension equality, including characteristic two. The change of coordinates is constant in the pencil variable, over the rational function field of the generic coefficients.

The same canonical conclusion holds for SL when m>n>0, when m<n<2m, and for every (n,m)=(2q+1,2), q≥0. The odd-state family has two minimal degrees q(q+2) and two Kronecker blocks of dimension 2q(q+2)+1, over every field. The case (5,2) is the corollary [8,8], with two 17-dimensional blocks. The actual SL matrix uses traceless coordinates, with a proved equivalence to the full SL equations.

Every proved generic pure Kronecker decomposition persists on a nonempty principal parameter locus over an infinite base field.

The generic square GL pencil is fully classified over every base field, after an explicitly injective coefficient extension. For n=m≥2, it has n distinct poles, each with one Jordan block of dimension 4 and n−2 blocks of dimension 2. The proof constructs the row diagonalization, verifies the resonances, and supplies a constant congruence with its inverse. For n=m=1, there is one regular block of dimension 2.

At every positive depth q with qm<n≤(q+1)m, the GL kernel has a proved reduced basis with degrees αᵢ+βⱼ+q, given the two actual auxiliary degree profiles. The polynomial right inverse and every generic rank and leading-coefficient condition are proved. The missing higher-depth profiles remain explicit inputs.

For every depth q, the maximal minors of the universal observability matrix (P, PM, ..., PM^(q−1)) have only unit common divisors when m ≥ 2 and n < qm. The same theorem holds for the generic affine pair over every base field. Cofactors determine the corank-one third-depth family and the exact bounded auxiliary relation dimensions in every corank-one depth. Other higher-depth degree lists remain open.

The corresponding universal and generic affine minor-coprimality theorems are also proved for every strictly wide stack qm<n, over every field, together with an actual polynomial right inverse. The proof combines separability and diagonalization with cyclic determinant identities and coefficient-field descent.

## Check the proofs

Install [elan](https://github.com/leanprover/elan), Git, and Python 3. From this repository, run:

```sh
lake exe cache get
python scripts/check.py
```

The verified inventory contains 524 Lean modules and 2,359 exported theorems. The toolchain and dependency files pin Lean and mathlib. The check builds every module and audits every theorem for axiom dependencies, allowing only `propext`, `Classical.choice`, and `Quot.sound`. Checks run in batches of at most 100 theorems, with both each batch and the complete inventory validated. Missing output or a failed process fails the audit. It rejects placeholder proofs, custom axioms, and `native_decide`. Temporary audit files go in `.verification/` and are not committed. GitHub Actions runs the same check.

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
