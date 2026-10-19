/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.RowNormalization
import FD56.Stabilizer.ChangeBasis

/-! Every full-row-rank pair admits the GL stabilizer reduction, without
assuming that its row matrix was already in standard coordinates. -/

noncomputable section
namespace FD56
open Matrix
variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem gl_surjective_reduction (M : Matrix n n K) (P : Matrix m n K)
    (hP : Function.Surjective P.mulVec) :
    ∃ (D : Matrix (Fin (Fintype.card n - Fintype.card m))
        (Fin (Fintype.card n - Fintype.card m)) K)
      (B : Matrix m (Fin (Fintype.card n - Fintype.card m)) K),
      Nonempty (glStabilizerSpace M P ≃ₗ[K] glStabilizerSpace D B) := by
  obtain ⟨S, I, hSI, hIS, hPS⟩ := surjective_matrix_normalization P hP
  let N := I * M * S
  have e₁ : glStabilizerSpace M P ≃ₗ[K]
      glStabilizerSpace N (Matrix.fromCols (1 : Matrix m m K) 0) := by
    have e := glChangeBasisEquiv M P S I hSI hIS
    rw [hPS] at e
    exact e
  have e₂ : glStabilizerSpace N (Matrix.fromCols (1 : Matrix m m K) 0) ≃ₗ[K]
      glStabilizerSpace N.toBlocks₂₂ N.toBlocks₁₂ := by
    have e := (glBlockEquiv N.toBlocks₁₁ N.toBlocks₁₂ N.toBlocks₂₁ N.toBlocks₂₂).symm
    rw [Matrix.fromBlocks_toBlocks] at e
    exact e
  exact ⟨N.toBlocks₂₂, N.toBlocks₁₂, ⟨e₁.trans e₂⟩⟩

theorem gl_surjective_dimension_reduction (M : Matrix n n K) (P : Matrix m n K)
    (hP : Function.Surjective P.mulVec) :
    ∃ (D : Matrix (Fin (Fintype.card n - Fintype.card m))
        (Fin (Fintype.card n - Fintype.card m)) K)
      (B : Matrix m (Fin (Fintype.card n - Fintype.card m)) K),
      Module.finrank K (glStabilizerSpace M P) = Module.finrank K (glStabilizerSpace D B) := by
  obtain ⟨D, B, ⟨e⟩⟩ := gl_surjective_reduction M P hP
  exact ⟨D, B, e.finrank_eq⟩

end FD56
