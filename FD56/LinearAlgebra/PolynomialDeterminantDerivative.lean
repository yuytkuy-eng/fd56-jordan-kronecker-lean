/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Trace

/-! Jacobi's formula for polynomial matrices over a commutative ring. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

omit [Fintype n] in
private theorem polynomial_derivative_finset_prod (s : Finset n) (f : n → R[X]) :
    derivative (∏ i ∈ s, f i) = ∑ i ∈ s, (∏ j ∈ s.erase i, f j) * derivative (f i) := by
  simpa only [Finset.prod, Finset.sum, Finset.erase_val] using
    (Polynomial.derivative_prod (s := s.val) (f := f))

theorem polynomial_det_derivative_columns (A : Matrix n n R[X]) :
    derivative A.det = ∑ i, (A.updateCol i (fun j => derivative (A j i))).det := by
  rw [Matrix.det_apply', Polynomial.derivative_sum]
  simp_rw [show ∀ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : R[X]) =
      C ((Equiv.Perm.sign σ : ℤ) : R) by intro σ; simp,
    Polynomial.derivative_C_mul, polynomial_derivative_finset_prod, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.det_apply']
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [Matrix.updateCol_self]
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  exact (Matrix.updateCol_ne (Finset.ne_of_mem_erase hj)).symm

theorem polynomial_det_derivative (A : Matrix n n R[X]) :
    derivative A.det = Matrix.trace (A.adjugate * A.map derivative) := by
  rw [polynomial_det_derivative_columns]
  unfold Matrix.trace Matrix.diag
  apply Finset.sum_congr rfl
  intro i _
  rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]
  rfl

theorem polynomial_det_derivative_comm (A : Matrix n n R[X]) :
    derivative A.det = Matrix.trace (A.map derivative * A.adjugate) := by
  rw [polynomial_det_derivative, Matrix.trace_mul_comm]

end FD56
