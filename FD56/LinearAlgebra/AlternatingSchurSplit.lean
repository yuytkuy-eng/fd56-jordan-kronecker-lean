/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.AlternatingRankTwoNilpotent
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Constant elimination of a nondegenerate alternating corner. -/

noncomputable section
namespace FD56
open Matrix

variable {K a b : Type*} [Field K] [Fintype a] [Fintype b]
  [DecidableEq a] [DecidableEq b]

def alternatingSchurChange (S : Matrix a a K) (C : Matrix a b K) :
    Matrix (a ⊕ b) (a ⊕ b) K := Matrix.fromBlocks 1 (- (S*C)) 0 1

theorem alternatingSchurChange_inverse (S : Matrix a a K) (C : Matrix a b K) :
    alternatingSchurChange S C * alternatingSchurChange (-S) C=1 := by
  simp [alternatingSchurChange,Matrix.fromBlocks_multiply,Matrix.fromBlocks_one]

theorem alternating_schur_split (A S : Matrix a a K) (C : Matrix a b K) (D : Matrix b b K)
    (hAS : A*S=1) (hSA : S*A=1) (hS : S.transpose = -S) :
    (alternatingSchurChange S C).transpose * Matrix.fromBlocks A C (-C.transpose) D *
      alternatingSchurChange S C = Matrix.fromBlocks A 0 0 (D+C.transpose*S*C) := by
  have hac : A * (-(S*C)) + C = 0 := by
    rw [Matrix.mul_neg,← Matrix.mul_assoc,hAS,Matrix.one_mul,neg_add_cancel]
  have hca : (-(S*C)).transpose*A-C.transpose=0 := by
    rw [Matrix.transpose_neg,Matrix.transpose_mul,hS,Matrix.mul_neg,neg_neg,
      Matrix.mul_assoc,hSA,Matrix.mul_one,sub_self]
  rw [alternatingSchurChange,Matrix.mul_assoc,Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_one,Matrix.mul_zero,Matrix.zero_mul,zero_add,add_zero,hac,
    Matrix.neg_mul,Matrix.mul_neg,neg_neg]
  rw [Matrix.fromBlocks_transpose,Matrix.fromBlocks_multiply]
  simp only [Matrix.transpose_one,Matrix.transpose_zero,Matrix.mul_one,Matrix.one_mul,
    Matrix.zero_mul,Matrix.mul_zero,zero_add,add_zero,← sub_eq_add_neg,hca]
  have hac' : -(A*(S*C)) + C=0 := by
    simpa only [Matrix.mul_neg] using hac
  rw [hac',Matrix.mul_zero,zero_add,Matrix.mul_assoc,add_comm]

theorem alternating_matrix_schur_split (B : Matrix (a ⊕ b) (a ⊕ b) K)
    (hB : ∀ w : a ⊕ b → K, w ⬝ᵥ (B *ᵥ w)=0)
    (S : Matrix a a K) (hAS : B.toBlocks₁₁*S=1) (hSA : S*B.toBlocks₁₁=1) :
    ∃ T U : Matrix (a ⊕ b) (a ⊕ b) K,
    ∃ D : Matrix b b K,
      T*U=1 ∧ U*T=1 ∧ T.transpose*B*T=Matrix.fromBlocks B.toBlocks₁₁ 0 0 D ∧
      (∀ w : b → K, w ⬝ᵥ (D *ᵥ w)=0) := by
  have hA : ∀ w : a → K, w ⬝ᵥ (B.toBlocks₁₁ *ᵥ w)=0 := by
    intro w
    have hh := hB (Sum.elim w 0)
    have he : B *ᵥ Sum.elim w 0 = Sum.elim (B.toBlocks₁₁ *ᵥ w) (B.toBlocks₂₁ *ᵥ w) := by
      conv_lhs => rw [← Matrix.fromBlocks_toBlocks B,Matrix.fromBlocks_mulVec]
      change Sum.elim (B.toBlocks₁₁ *ᵥ w+B.toBlocks₁₂ *ᵥ 0)
        (B.toBlocks₂₁ *ᵥ w+B.toBlocks₂₂ *ᵥ 0)=_
      simp
    rw [he,sumElim_dotProduct_sumElim,zero_dotProduct,add_zero] at hh
    exact hh
  have hS := alternating_matrix_transpose S (matrix_right_inverse_alternating _ S hAS hA)
  have hlower : B.toBlocks₂₁ = - B.toBlocks₁₂.transpose := by
    have hh := alternating_matrix_transpose B hB
    ext i j
    exact congrArg (fun M => M (Sum.inl j) (Sum.inr i)) hh
  let T := alternatingSchurChange S B.toBlocks₁₂
  let U := alternatingSchurChange (-S) B.toBlocks₁₂
  let D := B.toBlocks₂₂ + B.toBlocks₁₂.transpose*S*B.toBlocks₁₂
  have he : T.transpose*B*T=Matrix.fromBlocks B.toBlocks₁₁ 0 0 D := by
    have hb : B=Matrix.fromBlocks B.toBlocks₁₁ B.toBlocks₁₂ (-B.toBlocks₁₂.transpose) B.toBlocks₂₂ := by
      rw [← hlower,Matrix.fromBlocks_toBlocks]
    rw [hb]
    exact alternating_schur_split _ _ _ _ hAS hSA hS
  refine ⟨T,U,D,alternatingSchurChange_inverse _ _,?_,he,?_⟩
  · simpa only [neg_neg] using alternatingSchurChange_inverse (-S) B.toBlocks₁₂
  · intro w
    have hh := matrix_congruence_alternating B T hB (Sum.elim 0 w)
    rw [he] at hh
    simpa [Matrix.fromBlocks_mulVec,dotProduct,Fintype.sum_sum_type,Function.comp_def] using hh

end FD56
