# Jordan–Kronecker invariants in Lean

[![Lean proofs](https://github.com/yuytkuy-eng/fd56-jordan-kronecker-lean/actions/workflows/lean.yml/badge.svg)](https://github.com/yuytkuy-eng/fd56-jordan-kronecker-lean/actions/workflows/lean.yml)

Lean formalization by Shifan Yu of Jordan–Kronecker invariants for general and special linear semidirect products.

The **generic GL classification is proved for every positive pair of sizes (n,m)**. For nondivisible sizes, [`generic_nondivisible_gl_formula`](FD56/Hilbert/GenericGLClassification.lean) gives the explicit minimal-degree list and a constant congruence of the whole pencil to its Kronecker blocks, over every base field. For divisible sizes, the library constructs the full Jordan decomposition after a coefficient-field extension.

The **general SL classification remains incomplete**. All positive divisible sizes are classified. For every positive nondivisible size, the pencil is purely Kronecker, with proved block count and total minimal degree. Individual degrees are known when m>n, when m<n<2m, and for every odd n with m=2, over every field. In characteristic zero they are also known for n=mq+1, n=mq+m−1, and (n,m)=(10,4). See [proof coverage](docs/FORMALIZATION_STATUS.md) for exact formulas, assumptions, and remaining cases.

Here generic means the universal affine pair over the rational function field of its independent coefficients. The GL proof compares the [differential rank of selected observability minors](FD56/Hilbert/GenericInteriorDifferentialRank.lean) with a [degree-dependent Plücker rank bound](FD56/LinearAlgebra/PluckerDegreeBalance.lean). This forces both [actual auxiliary degree lists to be balanced](FD56/Hilbert/GenericInteriorDegreeBalance.lean); [GenericAllDepthGL](FD56/Hilbert/GenericAllDepthGL.lean) reconstructs the reduced kernel basis and full constant congruence. The separate [monomial Plücker chart](FD56/Hilbert/MonomialPluckerChart.lean) is a polynomial certificate; its realization as a generic SL pencil remains to be proved.

## Check the proofs

Install [elan](https://github.com/leanprover/elan), Git, and Python 3. From this repository, run:

```sh
lake exe cache get
python scripts/check.py
```

The library contains 785 Lean modules and 3,185 exported theorems. The checker builds every module and audits every exported theorem, allowing only `propext`, `Classical.choice`, and `Quot.sound`. It validates each batch and the complete inventory, rejects missing output or failed processes, and rejects placeholder proofs, custom axioms, and `native_decide`. Temporary audit files stay in `.verification/`. GitHub Actions runs the same check.

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
