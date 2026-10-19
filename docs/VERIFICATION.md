# Verification record

The included mathematical sources were checked with Lean 4.19.0 and mathlib commit c44e0c8ee63ca166450922a373c7409c5d26b00b on 2026-10-19.

The local Lake build and the sixteen-theorem axiom audit passed. Because Git transport was unreliable on the build machine, that build used local mirrors of the exact dependency revisions obtained from official GitHub archives and the official mathlib compilation cache. No mathematical source was modified to accommodate the mirrors. Local paths and mirror configuration are excluded from this repository.

The published configuration uses pinned Git dependencies. To reproduce the checks, run the commands in the [README](../README.md). A local mirror build is evidence of checking the included proofs; it is not a recorded fresh build of the published Git dependency configuration on every platform.

## Trust and scope

- Twelve Lean source files contain sixty-three theorem declarations.
- No source uses placeholder proofs, custom axioms, or native evaluation as a proof.
- [Audit.lean](../Audit.lean) prints dependencies for sixteen central theorems.
- [The recorded audit](../verification/axioms.txt) lists only `propext`, `Classical.choice`, and `Quot.sound` for the noncomputational results. `FD56.table_64_28` has no axiom dependencies.
- [The verification manifest](../verification/verification.json) records the checked scope and SHA-256 hashes of the Lean sources and build configuration.

The full manuscript and the generic GL/SL classification are not yet formalized. The detailed boundary is recorded in [formalization status](FORMALIZATION_STATUS.md).

The GitHub Actions workflow builds the pinned configuration and runs the audit on pushes and pull requests. Its presence alone is not evidence that a remote run passed.
