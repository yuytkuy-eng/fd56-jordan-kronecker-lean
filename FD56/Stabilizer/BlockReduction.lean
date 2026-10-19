/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.RankOne
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-! Exact block reduction of the GL stabilizer equations on a full-row-rank
chart P = [I 0]. This is the algebraic step in the nullity induction. -/

namespace FD56
open Matrix
variable {R m r : Type*} [CommRing R] [Fintype m] [Fintype r]
  [DecidableEq m]

theorem gl_block_reduction (A : Matrix m m R) (B : Matrix m r R)
    (C : Matrix r m R) (D : Matrix r r R)
    (X₁₁ : Matrix m m R) (X₁₂ : Matrix m r R)
    (E : Matrix r m R) (G : Matrix r r R)
    (U₁ : Matrix m m R) (U₂ : Matrix r m R) :
    (Matrix.fromCols (1 : Matrix m m R) (0 : Matrix m r R) *
        Matrix.fromBlocks X₁₁ X₁₂ E G = 0 ∧
      Matrix.fromBlocks A B C D * Matrix.fromBlocks X₁₁ X₁₂ E G -
        Matrix.fromBlocks X₁₁ X₁₂ E G * Matrix.fromBlocks A B C D =
        Matrix.fromRows U₁ U₂ * Matrix.fromCols (1 : Matrix m m R) (0 : Matrix m r R)) ↔
      X₁₁ = 0 ∧ X₁₂ = 0 ∧ B * G = 0 ∧ D * G - G * D = E * B ∧
        U₁ = B * E ∧ U₂ = D * E - E * A - G * C := by
  constructor
  · rintro ⟨hP, hM⟩
    have hp' : Matrix.fromCols X₁₁ X₁₂ = Matrix.fromCols (0 : Matrix m m R) (0 : Matrix m r R) := by
      simpa only [Matrix.fromCols_mul_fromBlocks, Matrix.one_mul, Matrix.zero_mul,
        add_zero, Matrix.fromCols_zero] using hP
    obtain ⟨h₁₁, h₁₂⟩ := Matrix.fromCols_inj hp'
    subst X₁₁
    subst X₁₂
    simp only [Matrix.fromBlocks_multiply, Matrix.fromRows_mul_fromCols,
      Matrix.zero_mul, Matrix.mul_zero, Matrix.mul_one, add_zero, zero_add,
      sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add, sub_zero, zero_sub, neg_zero] at hM
    obtain ⟨h₁, h₂, h₃, h₄⟩ := Matrix.fromBlocks_inj.mp hM
    refine ⟨rfl, rfl, h₂, ?_, h₁.symm, ?_⟩
    · apply sub_eq_zero.mp
      convert h₄ using 1; abel
    · rw [← h₃]
      abel
  · rintro ⟨rfl, rfl, hBG, hDG, rfl, rfl⟩
    constructor
    · simp [Matrix.fromCols_mul_fromBlocks]
    · simp only [Matrix.fromBlocks_multiply, Matrix.fromRows_mul_fromCols,
        Matrix.zero_mul, Matrix.mul_zero, Matrix.mul_one, add_zero, zero_add,
        sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add, sub_zero, zero_sub, neg_zero]
      apply Matrix.fromBlocks_inj.mpr
      refine ⟨rfl, hBG, ?_, ?_⟩
      · abel
      · calc
          _ = (D * G - G * D) - E * B := by abel
          _ = 0 := sub_eq_zero.mpr hDG

end FD56
