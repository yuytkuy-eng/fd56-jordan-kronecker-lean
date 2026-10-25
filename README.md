# Jordan–Kronecker invariants in Lean

[![Lean proofs](https://github.com/yuytkuy-eng/fd56-jordan-kronecker-lean/actions/workflows/lean.yml/badge.svg)](https://github.com/yuytkuy-eng/fd56-jordan-kronecker-lean/actions/workflows/lean.yml)

Partial Lean formalization by Shifan Yu, concerning general and special linear semidirect products.

The library determines actual reduced polynomial kernel-basis degrees for GL and SL when m ≥ n (SL: n > 0), every GL list with m < n < 3m, and every SL degree multiplicity with m < n ≤ 2m. The GL polynomial kernel vanishes whenever n is a positive multiple of m. These results hold over every field.

At depth three, all sizes (n,m)=((4a−1)k,ak), a≥2 and k≥1, are covered over every field. In particular, (7k,2k) has k² degrees equal to 31, and (11k,3k) has 2k² degrees equal to 38. In characteristic zero, (10k,3k) has 2k² degrees equal to 32. **The complete generic GL/SL classification is not formalized.** See [proof coverage](docs/FORMALIZATION_STATUS.md) for formulas, assumptions, and remaining work.

For every depth q, the maximal minors of the universal observability matrix (P, PM, ..., PM^(q−1)) have only unit common divisors when m ≥ 2 and n < qm. The same theorem holds for the generic affine pair over every base field. A cofactor argument uses this result to determine the corank-one third-depth family. Other higher-depth degree lists remain open.

## Check the proofs

Install [elan](https://github.com/leanprover/elan), Git, and Python 3. From this repository, run:

```sh
lake exe cache get
python scripts/check.py
```

The toolchain and dependency files pin Lean and mathlib. The check builds every module and audits every theorem for axiom dependencies, allowing only `propext`, `Classical.choice`, and `Quot.sound`. It rejects placeholder proofs, custom axioms, and `native_decide`. Temporary audit files go in `.verification/` and are not committed. GitHub Actions runs the same check.

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
