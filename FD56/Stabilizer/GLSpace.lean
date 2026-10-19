/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.BlockReduction

/-! Linear equivalence of GL stabilizer spaces under block reduction. -/

noncomputable section
namespace FD56
open Matrix
variable {R n m r : Type*} [CommRing R] [Fintype n] [Fintype m] [Fintype r]

def glStabilizerSpace (M : Matrix n n R) (P : Matrix m n R) :
    Submodule R (Matrix n n R × Matrix n m R) where
  carrier := {z | P * z.1 = 0 ∧ M * z.1 - z.1 * M = z.2 * P}
  zero_mem' := by simp
  add_mem' := by
    rintro z w ⟨hzP, hzM⟩ ⟨hwP, hwM⟩
    constructor
    · change P * (z.1 + w.1) = 0
      simp [Matrix.mul_add, hzP, hwP]
    · change M * (z.1 + w.1) - (z.1 + w.1) * M = (z.2 + w.2) * P
      simp only [Matrix.mul_add, Matrix.add_mul]
      calc
        _ = (M * z.1 - z.1 * M) + (M * w.1 - w.1 * M) := by abel
        _ = _ := by rw [hzM, hwM]
  smul_mem' := by
    rintro c z ⟨hzP, hzM⟩
    constructor
    · change P * (c • z.1) = 0
      simp [Matrix.mul_smul, hzP]
    · change M * (c • z.1) - (c • z.1) * M = (c • z.2) * P
      rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, hzM, Matrix.smul_mul]

variable [DecidableEq m]

theorem gl_block_coordinates (A : Matrix m m R) (B : Matrix m r R)
    (C : Matrix r m R) (D : Matrix r r R)
    (X : Matrix (m ⊕ r) (m ⊕ r) R) (U : Matrix (m ⊕ r) m R) :
    (X,U) ∈ glStabilizerSpace (Matrix.fromBlocks A B C D)
      (Matrix.fromCols (1 : Matrix m m R) (0 : Matrix m r R)) ↔
    X.toBlocks₁₁ = 0 ∧ X.toBlocks₁₂ = 0 ∧
      (X.toBlocks₂₂, X.toBlocks₂₁) ∈ glStabilizerSpace D B ∧
      U.toRows₁ = B * X.toBlocks₂₁ ∧
      U.toRows₂ = D * X.toBlocks₂₁ - X.toBlocks₂₁ * A - X.toBlocks₂₂ * C := by
  have h := gl_block_reduction A B C D X.toBlocks₁₁ X.toBlocks₁₂
    X.toBlocks₂₁ X.toBlocks₂₂ U.toRows₁ U.toRows₂
  change (_ ∧ _) ↔ _ ∧ _ ∧ (_ ∧ _) ∧ _ ∧ _
  simpa only [Matrix.fromBlocks_toBlocks, Matrix.fromRows_toRows, and_assoc] using h

def glBlockEquiv (A : Matrix m m R) (B : Matrix m r R)
    (C : Matrix r m R) (D : Matrix r r R) :
    glStabilizerSpace D B ≃ₗ[R]
      glStabilizerSpace (Matrix.fromBlocks A B C D)
        (Matrix.fromCols (1 : Matrix m m R) (0 : Matrix m r R)) where
  toFun z := ⟨(Matrix.fromBlocks 0 0 z.val.2 z.val.1,
    Matrix.fromRows (B * z.val.2) (D * z.val.2 - z.val.2 * A - z.val.1 * C)), by
      apply (gl_block_coordinates A B C D _ _).mpr
      exact ⟨rfl, rfl, z.property, rfl, rfl⟩⟩
  invFun z := ⟨(z.val.1.toBlocks₂₂, z.val.1.toBlocks₂₁),
    ((gl_block_coordinates A B C D _ _).mp z.property).2.2.1⟩
  left_inv z := by apply Subtype.ext; rfl
  right_inv z := by
    obtain ⟨h11, h12, _, hu1, hu2⟩ := (gl_block_coordinates A B C D _ _).mp z.property
    apply Subtype.ext
    apply Prod.ext
    · change Matrix.fromBlocks 0 0 z.val.1.toBlocks₂₁ z.val.1.toBlocks₂₂ = z.val.1
      simpa only [h11, h12] using Matrix.fromBlocks_toBlocks z.val.1
    · change Matrix.fromRows (B * z.val.1.toBlocks₂₁)
        (D * z.val.1.toBlocks₂₁ - z.val.1.toBlocks₂₁ * A - z.val.1.toBlocks₂₂ * C) = z.val.2
      rw [← hu1, ← hu2, Matrix.fromRows_toRows]
  map_add' z w := by
    apply Subtype.ext
    apply Prod.ext
    · apply Matrix.ext
      intro i j
      cases i <;> cases j <;> simp [Matrix.fromBlocks]
    · apply Matrix.ext
      intro i j
      cases i <;>
        simp [Matrix.fromRows, Matrix.mul_add, Matrix.add_mul, Matrix.sub_apply]
      abel
  map_smul' c z := by
    apply Subtype.ext
    apply Prod.ext
    · apply Matrix.ext
      intro i j
      cases i <;> cases j <;> simp [Matrix.fromBlocks]
    · apply Matrix.ext
      intro i j
      cases i <;>
        simp [Matrix.fromRows, Matrix.mul_smul, Matrix.smul_mul, smul_sub, mul_sub]

theorem gl_block_finrank (A : Matrix m m R) (B : Matrix m r R)
    (C : Matrix r m R) (D : Matrix r r R) :
    Module.finrank R (glStabilizerSpace (Matrix.fromBlocks A B C D)
      (Matrix.fromCols (1 : Matrix m m R) (0 : Matrix m r R))) =
      Module.finrank R (glStabilizerSpace D B) :=
  (glBlockEquiv A B C D).finrank_eq.symm

end FD56
