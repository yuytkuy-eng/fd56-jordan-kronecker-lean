# Jordan–Kronecker invariants in Lean

[![Lean proofs](https://github.com/yuytkuy-eng/fd56-jordan-kronecker-lean/actions/workflows/lean.yml/badge.svg)](https://github.com/yuytkuy-eng/fd56-jordan-kronecker-lean/actions/workflows/lean.yml)

Partial Lean formalization by Shifan Yu, concerning general and special linear semidirect products.

The library determines actual reduced polynomial kernel-basis degrees throughout m ≥ n (SL: n > 0), for GL when m < n < 2m, and for SL when n = m + 1 with m > 0. It determines both lists for the `(11k, 8k)` family and the SL list for every uniform family `m = ar`, `n = (a + 1)r`, with a,r > 0. For a ≥ 2 the uniform SL list is balanced; for n = 2m it is the singleton [3m − 1]. It also determines the SL list for all nonuniform pairs `m = a(u+v)+v`, `n = m+u+v`, with a ≥ 4 and u,v > 0. These results hold over every field. **The complete generic GL/SL classification is not formalized.** See [proof coverage](docs/FORMALIZATION_STATUS.md) for formulas, assumptions, and remaining work.

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
