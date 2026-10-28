/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.MatrixDeterminantDerivation
import FD56.Stabilizer.ObservabilityScalarAdjugate

/-! Every coefficient derivation of an observability minor pairs with its adjugate scalar lift. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {B R n m : Type*} [CommRing B] [CommRing R] [Algebra B R] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

private theorem matrixCommutatorSum_succ (M D : Matrix n n R) (l : ℕ) :
    matrixCommutatorSum M D (l+1) = matrixCommutatorSum M D l*M+M^l*D := by
  unfold matrixCommutatorSum
  rw [Finset.sum_range_succ, Finset.sum_mul]
  simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, Matrix.mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  have h : l-s=(l-1-s)+1 := by have := Finset.mem_range.mp hs; omega
  rw [h, pow_succ]
  simp only [Matrix.mul_assoc]

theorem matrix_derivation_pow (D : Derivation B R R) (M : Matrix n n R) (l : ℕ) :
    (M^l).map D = matrixCommutatorSum M (M.map D) l := by
  induction l with
  | zero =>
    funext i j
    by_cases h : i=j <;> simp [matrixCommutatorSum, Matrix.one_apply, h]
  | succ l ih =>
    rw [pow_succ, matrix_derivation_mul D, ih, matrixCommutatorSum_succ]

private theorem matrixCommutatorSum_trace (M D A : Matrix n n R) (l : ℕ) :
    Matrix.trace (matrixCommutatorSum M D l*A) =
      Matrix.trace (D*matrixCommutatorSum M A l) := by
  unfold matrixCommutatorSum
  rw [Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum, Matrix.trace_sum]
  rw [← Finset.sum_range_reflect (fun s => Matrix.trace (D*(M^s*A*M^(l-1-s)))) l]
  apply Finset.sum_congr rfl
  intro s hs
  have h : l-1-(l-1-s)=s := by have := Finset.mem_range.mp hs; omega
  rw [h]
  calc
    Matrix.trace (M^s*D*M^(l-1-s)*A) = Matrix.trace ((D*M^(l-1-s)*A)*M^s) := by
      simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (M^s) (D*M^(l-1-s)*A)
    _ = Matrix.trace (D*(M^(l-1-s)*A*M^s)) := by simp only [Matrix.mul_assoc]

omit [DecidableEq n] in
private theorem trace_observabilityScalarColumn (A : Matrix m n R)
    (N : Matrix n n R) (row : n → m) (k : n) :
    Matrix.trace (A*observabilityScalarColumn N row k) = (A*N) (row k) k := by
  rw [mul_observabilityScalarColumn]
  simp [Matrix.trace, Matrix.diag]

theorem observabilitySelectedMatrix_det_derivation (D : Derivation B R R)
    (M : Matrix n n R) (P : Matrix m n R) (level : n → ℕ) (row : n → m) :
    D (observabilitySelectedMatrix M P level row).det =
      Matrix.trace (M.map D * observabilityScalarX M P
        (observabilitySelectedMatrix M P level row).adjugate level row) +
      Matrix.trace (P.map D * observabilityScalarU M
        (observabilitySelectedMatrix M P level row).adjugate level row) := by
  let N := (observabilitySelectedMatrix M P level row).adjugate
  rw [matrix_det_derivation_comm]
  change Matrix.trace ((observabilitySelectedMatrix M P level row).map D*N) = _
  have hrow (k : n) :
      ((observabilitySelectedMatrix M P level row).map D*N) k k =
        ((P.map D*M^(level k)+
          P*matrixCommutatorSum M (M.map D) (level k))*N) (row k) k := by
    have h := matrix_derivation_mul D P (M^(level k))
    rw [matrix_derivation_pow] at h
    change (∑ j, D ((P*M^(level k)) (row k) j)*N j k) = _
    simp only [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg (fun z => z*N j k) (congrFun (congrFun h (row k)) j)
  calc
    Matrix.trace ((observabilitySelectedMatrix M P level row).map D*N) =
        ∑ k, Matrix.trace ((P.map D*M^(level k)+
          P*matrixCommutatorSum M (M.map D) (level k))*observabilityScalarColumn N row k) := by
      change (∑ k, ((observabilitySelectedMatrix M P level row).map D*N) k k) = _
      apply Finset.sum_congr rfl
      intro k _
      rw [hrow, trace_observabilityScalarColumn]
    _ = ∑ k, (Matrix.trace (M.map D*
          matrixCommutatorSum M (observabilityScalarColumn N row k*P) (level k)) +
        Matrix.trace (P.map D*(M^(level k)*observabilityScalarColumn N row k))) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Matrix.add_mul, Matrix.trace_add]
      rw [Matrix.trace_mul_cycle P, Matrix.trace_mul_comm (observabilityScalarColumn N row k*P),
        matrixCommutatorSum_trace]
      simp only [Matrix.mul_assoc]
      exact add_comm _ _
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp only [observabilityScalarX, observabilityScalarU, Matrix.mul_sum, Matrix.trace_sum, N]

end FD56
