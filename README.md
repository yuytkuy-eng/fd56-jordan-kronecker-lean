# Jordan–Kronecker invariants: Lean formalization

Lean 4 proofs accompanying *Jordan–Kronecker invariants of general and special linear semidirect products*, by Shifan Yu.

**Status: partial formalization.** All 63 theorem declarations in this project have been checked by Lean. The full generic GL/SL classification is not yet formalized.

The main verified result is a degree-five kernel construction for the `(11k, 8k)` family and an obstruction to a balanced Hilbert profile of the full SL Kirillov radical. The project also verifies arithmetic identities for the proposed spectrum formulas.

## Main result

Let `K` be a field and `k > 0`. Let `M` be an `11k × 11k` polynomial matrix and `P` an `8k × 11k` polynomial matrix. Assume their entries have degree at most one and the rows of `P` are linearly independent over `K[t]`.

`FD56.family_has_degree_five_stabilizer` constructs matrices `X ≠ 0` and `U`, with entries of degree at most five, such that

```text
P X = 0
M X − X M = U P
trace X = 0.
```

`FD56.family_no_balanced_profile` proves that the full SL Kirillov radical cannot have a balanced Hilbert profile with `15k² + 1` indices whose sum is `97k² − 1`. The actual degree-five kernel dimension is positive, whereas every such balanced profile gives dimension zero at degree five.

See [formalization status](docs/FORMALIZATION_STATUS.md) for the precise scope and remaining proofs.

## Build

Install Git and [elan](https://github.com/leanprover/elan), then run:

```sh
git clone https://github.com/yuytkuy-eng/fd56-jordan-kronecker-lean.git
cd fd56-jordan-kronecker-lean
lake exe cache get
lake build
lake env lean -j1 -s65536 Audit.lean
```

The project pins Lean **4.19.0** and mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The committed Lake manifest also pins transitive dependencies. The first build downloads the toolchain, dependencies, and compilation cache.

## Source map

| Module | Verified content |
| --- | --- |
| [PolynomialMatrix](FD56/PolynomialMatrix.lean) | Degree bounds, truncated polynomial spaces, dimensions, nonzero kernels |
| [RankOne](FD56/RankOne.lean) | Rank-one construction, nonvanishing, stabilizer equations, trace zero |
| [LowDegree](FD56/LowDegree.lean) | Coefficient maps, dimension criteria, degree-five construction |
| [Kirillov](FD56/Kirillov.lean) | Kirillov pairing and inclusion in the full SL radical |
| [HilbertObstruction](FD56/HilbertObstruction.lean) | Actual bounded radical dimensions and balanced-profile obstruction |
| [SpectrumArithmetic](FD56/SpectrumArithmetic.lean) | Candidate formulas, lengths, sums, block dimensions, six examples |
| [HilbertArithmetic](FD56/HilbertArithmetic.lean) | Numerical Hilbert-function branches and balanced-list identities |
| [TraceAnnihilator](FD56/TraceAnnihilator.lean) | Exact full SL radical equations, including the scalar correction |
| [HyperplaneRadical](FD56/HyperplaneRadical.lean) | Radical dimension under hyperplane restriction |
| [HilbertRecovery](FD56/HilbertRecovery.lean) | Recovery of a finite index list from its Hilbert function |
| [Audit](Audit.lean) | Axiom dependencies for sixteen central theorems |

## Verification

The included sources contain no placeholder proofs, custom axioms, or `native_decide`. The audited theorems use only the standard foundations `propext`, `Classical.choice`, and `Quot.sound`; the audited table calculation has no axiom dependencies.

[Verification notes](docs/VERIFICATION.md) explain the recorded build and audit. Machine-readable evidence and source hashes are in [verification/](verification/).

## License

Copyright 2026 Shifan Yu. Licensed under [Apache-2.0](LICENSE); see [NOTICE](NOTICE). Dependencies retain their respective licenses.
