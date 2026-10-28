/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.MatrixDeterminantDifferential
import FD56.Stabilizer.ObservabilityDeterminantDerivation

/-! The output part of the selected-minor differential is the explicit
scalar-lift trace pairing, for arbitrary polynomial or scalar variations. -/

noncomputable section
namespace FD56
open Matrix
open scoped BigOperators
variable {R n m : Type*} [CommRing R]
  [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

omit [DecidableEq n] in
private theorem output_trace_column (Q : Matrix m n R) (N : Matrix n n R)
    (row : n → m) (k : n) :
    Matrix.trace (Q*observabilityScalarColumn N row k)=(Q*N) (row k) k := by
  rw [mul_observabilityScalarColumn]
  simp [Matrix.trace,Matrix.diag]

theorem observabilitySelectedMatrix_output_differential
    (M : Matrix n n R) (P Q : Matrix m n R) (level : n → ℕ) (row : n → m) :
    matrixDetDifferential (observabilitySelectedMatrix M P level row)
      (observabilitySelectedMatrix M Q level row)=
      Matrix.trace (Q*observabilityScalarU M
        (observabilitySelectedMatrix M P level row).adjugate level row) := by
  let N := (observabilitySelectedMatrix M P level row).adjugate
  rw [matrixDetDifferential,Matrix.trace_mul_comm]
  change Matrix.trace (observabilitySelectedMatrix M Q level row*N)=_
  calc
    Matrix.trace (observabilitySelectedMatrix M Q level row*N)=
        ∑ k, Matrix.trace ((Q*M^(level k))*observabilityScalarColumn N row k) := by
      change (∑ k, (observabilitySelectedMatrix M Q level row*N) k k)=_
      apply Finset.sum_congr rfl
      intro k _
      rw [output_trace_column]
      rfl
    _ = _ := by
      simp only [observabilityScalarU,Matrix.mul_sum,Matrix.trace_sum,N,Matrix.mul_assoc]

end FD56
