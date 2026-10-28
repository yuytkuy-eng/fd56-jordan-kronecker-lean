/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Trace

/-! Determinant and matrix product rules for arbitrary coefficient derivations. -/

noncomputable section
namespace FD56
open Matrix
open scoped BigOperators
variable {R A n : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [Fintype n] [DecidableEq n]

omit [Fintype n] in
theorem derivation_finset_prod (D : Derivation R A A) (s : Finset n) (f : n → A) :
    D (∏ i ∈ s, f i) = ∑ i ∈ s, (∏ j ∈ s.erase i, f j) * D (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha,D.leibniz,smul_eq_mul,smul_eq_mul,ih,
      Finset.sum_insert ha,Finset.erase_insert ha,Finset.mul_sum,add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hai : a≠i := fun h => ha (h ▸ hi)
    rw [Finset.erase_insert_of_ne hai,Finset.prod_insert
      (fun h => ha (Finset.mem_of_mem_erase h)),mul_assoc]

theorem matrix_det_derivation_columns (D : Derivation R A A) (M : Matrix n n A) :
    D M.det = ∑ i, (M.updateCol i (fun j => D (M j i))).det := by
  rw [Matrix.det_apply',map_sum]
  simp_rw [D.leibniz,smul_eq_mul,D.map_intCast,mul_zero,add_zero,
    derivation_finset_prod,Finset.mul_sum]
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

theorem matrix_det_derivation (D : Derivation R A A) (M : Matrix n n A) :
    D M.det = Matrix.trace (M.adjugate * M.map D) := by
  rw [matrix_det_derivation_columns]
  unfold Matrix.trace Matrix.diag
  apply Finset.sum_congr rfl
  intro i _
  rw [← Matrix.cramer_apply,Matrix.cramer_eq_adjugate_mulVec]
  rfl

theorem matrix_det_derivation_comm (D : Derivation R A A) (M : Matrix n n A) :
    D M.det = Matrix.trace (M.map D * M.adjugate) := by
  rw [matrix_det_derivation,Matrix.trace_mul_comm]

theorem matrix_derivation_mul {a b c : Type*} [Fintype b]
    (D : Derivation R A A) (M : Matrix a b A) (N : Matrix b c A) :
    (M*N).map D = M.map D*N+M*N.map D := by
  ext i j
  simp only [Matrix.map_apply,Matrix.mul_apply,Matrix.add_apply,map_sum,D.leibniz,
    smul_eq_mul,Finset.sum_add_distrib]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

end FD56
