/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.AlternatingCongruence
import FD56.LinearAlgebra.BilinearPrimaryRestriction

/-! The relative operator of a regular alternating pencil is self-adjoint. -/

noncomputable section
namespace FD56
open Matrix
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

theorem alternating_operator_self_adjoint (B T : Matrix n n K)
    (hB : ∀ v, v ⬝ᵥ (B *ᵥ v)=0) (hBT : ∀ v, v ⬝ᵥ ((B*T) *ᵥ v)=0) :
    ∀ x y, B.toBilin' (T.toLin' x) y=B.toBilin' x (T.toLin' y) := by
  have ht : T.transpose*B=B*T := by
    have h := alternating_matrix_transpose (B*T) hBT
    rw [Matrix.transpose_mul,alternating_matrix_transpose B hB,Matrix.mul_neg] at h
    exact neg_injective h
  intro x y
  simp only [Matrix.toBilin'_apply',Matrix.toLin'_apply]
  rw [dotProduct_mulVec,vecMul_mulVec,ht,← dotProduct_mulVec,Matrix.mulVec_mulVec]

theorem alternating_pencil_operator_forms (A B : Matrix n n K)
    (hA : ∀ v, v ⬝ᵥ (A *ᵥ v)=0) (hB : ∀ v, v ⬝ᵥ (B *ᵥ v)=0)
    (hd : B.det≠0) :
    let f := Matrix.toLin' (-B⁻¹*A)
    B.toBilin'.Nondegenerate ∧ B.toBilin'.IsAlt ∧
      (∀ x, B.toBilin' x (f x)=0) ∧
      ∀ x y, B.toBilin' (f x) y=B.toBilin' x (f y) := by
  have hBA : B*(-B⁻¹*A) = -A := by
    rw [← Matrix.mul_assoc,Matrix.mul_neg,Matrix.mul_nonsing_inv B (isUnit_iff_ne_zero.mpr hd),
      Matrix.neg_mul,Matrix.one_mul]
  have hBT : ∀ v, v ⬝ᵥ ((B*(-B⁻¹*A)) *ᵥ v)=0 := by
    intro v
    rw [hBA,Matrix.neg_mulVec,dotProduct_neg,hA,neg_zero]
  refine ⟨LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' B hd,?_,?_,
    alternating_operator_self_adjoint B _ hB hBT⟩
  · intro x
    simpa only [Matrix.toBilin'_apply'] using hB x
  · intro x
    simpa only [Matrix.toBilin'_apply',Matrix.toLin'_apply,Matrix.mulVec_mulVec] using hBT x

end FD56
