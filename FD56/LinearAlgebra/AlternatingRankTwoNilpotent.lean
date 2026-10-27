/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.AlternatingRankTwo
import Mathlib.RingTheory.Nilpotent.Basic

/-! A nilpotent product of alternating forms, one of rank two, has square zero. -/

noncomputable section
namespace FD56
open Matrix

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

theorem matrix_mul_outer (A : Matrix n n K) (u v : n → K) :
    A * Matrix.vecMulVec u v = Matrix.vecMulVec (A *ᵥ u) v := by
  ext i j
  simp only [Matrix.mul_apply,Matrix.vecMulVec_apply,Matrix.mulVec,dotProduct,
    Finset.sum_mul,mul_assoc]

theorem matrix_outer_mul_outer (u v w z : n → K) :
    Matrix.vecMulVec u v * Matrix.vecMulVec w z =
      (v ⬝ᵥ w) • Matrix.vecMulVec u z := by
  ext i j
  simp only [Matrix.mul_apply,Matrix.vecMulVec_apply,Matrix.smul_apply,smul_eq_mul,
    dotProduct,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem decomposable_alternating_product_square (C : Matrix n n K) (u v : n → K)
    (hC : ∀ w : n → K, w ⬝ᵥ (C *ᵥ w) = 0) :
    (C * (Matrix.vecMulVec u v - Matrix.vecMulVec v u)) ^ 2 =
      (v ⬝ᵥ (C *ᵥ u)) • (C * (Matrix.vecMulVec u v - Matrix.vecMulVec v u)) := by
  have hpair : u ⬝ᵥ (C *ᵥ v) = -(v ⬝ᵥ (C *ᵥ u)) := by
    have h := hC (u + v)
    simp only [Matrix.mulVec_add,add_dotProduct,dotProduct_add,hC,zero_add,add_zero] at h
    exact eq_neg_of_add_eq_zero_left ((add_comm _ _).trans h)
  rw [Matrix.mul_sub,matrix_mul_outer,matrix_mul_outer,pow_two,
    Matrix.sub_mul,Matrix.mul_sub,Matrix.mul_sub]
  rw [matrix_outer_mul_outer,matrix_outer_mul_outer,matrix_outer_mul_outer,
    matrix_outer_mul_outer,hC,hC,hpair]
  ext i j
  simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,zero_mul]
  ring

theorem nilpotent_matrix_square_zero_of_square_smul (A : Matrix n n K) (c : K)
    (hs : A ^ 2 = c • A) (hn : IsNilpotent A) : A ^ 2 = 0 := by
  have hp (k : ℕ) : A ^ (k + 1) = c ^ k • A := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ,ih,Matrix.smul_mul,← pow_two,hs,smul_smul]
      congr 1
      exact (pow_succ c k).symm
  obtain ⟨k,hk⟩ := hn
  have hz : c ^ k • A = 0 := by
    rw [← hp,pow_succ,hk,Matrix.zero_mul]
  by_cases hc : c = 0
  · simp [hs,hc]
  · have hA : A = 0 := (smul_eq_zero.mp hz).resolve_left (pow_ne_zero k hc)
    simp [hA]

theorem alternating_rank_two_nilpotent_square_zero (C A : Matrix n n K)
    (hC : ∀ w : n → K, w ⬝ᵥ (C *ᵥ w) = 0)
    (hA : ∀ w : n → K, w ⬝ᵥ (A *ᵥ w) = 0)
    (hr : Module.finrank K (LinearMap.range (Matrix.toLin' A)) ≤ 2)
    (hn : IsNilpotent (C*A)) : (C*A)^2=0 := by
  by_cases hz : A=0
  · simp [hz]
  · obtain ⟨i,j,hij⟩ : ∃ i j, A i j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hz (by ext i j; exact h i j)
    obtain ⟨u,v,he⟩ := alternating_rank_two_decomposable A hA hr i j hij
    rw [he] at hn ⊢
    exact nilpotent_matrix_square_zero_of_square_smul _ _
      (decomposable_alternating_product_square C u v hC) hn

theorem matrix_right_inverse_alternating (B V : Matrix n n K) (hBV : B*V=1)
    (hB : ∀ w : n → K, w ⬝ᵥ (B *ᵥ w) = 0) :
    ∀ w : n → K, w ⬝ᵥ (V *ᵥ w) = 0 := by
  intro w
  have hh := hB (V *ᵥ w)
  rw [Matrix.mulVec_mulVec,hBV,Matrix.one_mulVec] at hh
  rwa [dotProduct_comm] at hh

theorem alternating_rank_two_nilpotent_ratio (A B V : Matrix n n K)
    (hBV : B*V=1)
    (hA : ∀ w : n → K, w ⬝ᵥ (A *ᵥ w) = 0)
    (hB : ∀ w : n → K, w ⬝ᵥ (B *ᵥ w) = 0)
    (hr : Module.finrank K (LinearMap.range (Matrix.toLin' A)) ≤ 2)
    (hn : IsNilpotent (V*A)) : (V*A)^2=0 :=
  alternating_rank_two_nilpotent_square_zero V A
    (matrix_right_inverse_alternating B V hBV hB) hA hr hn

end FD56
