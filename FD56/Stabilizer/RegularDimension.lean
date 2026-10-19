/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.Observability
import FD56.Stabilizer.Reduction
import FD56.Stabilizer.GLBase

/-! The GL stabilizer dimension follows from two consecutive observability
kernel dimensions. The stabilizer dimension itself is not an assumption. -/

noncomputable section
namespace FD56
open Matrix

theorem gl_observability_reduction {K n m : Type*} [Field K]
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (M : Matrix n n K) (P : Matrix m n K) (hP : Function.Surjective P.mulVec) :
    ∃ (D : Matrix (Fin (Fintype.card n - Fintype.card m))
        (Fin (Fintype.card n - Fintype.card m)) K)
      (B : Matrix m (Fin (Fintype.card n - Fintype.card m)) K),
      Module.finrank K (glStabilizerSpace M P) = Module.finrank K (glStabilizerSpace D B) ∧
      ∀ q, Module.finrank K (unobservableSpace M P (q + 1)) =
        Module.finrank K (unobservableSpace D B q) := by
  obtain ⟨S, I, hSI, hIS, hPS⟩ := surjective_matrix_normalization P hP
  let N := I * M * S
  refine ⟨N.toBlocks₂₂, N.toBlocks₁₂, ?_, ?_⟩
  · have h := gl_change_basis_finrank M P S I hSI hIS
    rw [hPS] at h
    have hb := gl_block_finrank N.toBlocks₁₁ N.toBlocks₁₂ N.toBlocks₂₁ N.toBlocks₂₂
    rw [Matrix.fromBlocks_toBlocks] at hb
    exact h.symm.trans hb
  · intro q
    have h := unobservable_change_basis_finrank M P S I hSI hIS (q + 1)
    rw [hPS] at h
    have hb := unobservable_block_finrank N.toBlocks₁₁ N.toBlocks₁₂ N.toBlocks₂₁ N.toBlocks₂₂ q
    rw [Matrix.fromBlocks_toBlocks] at hb
    exact h.symm.trans hb

theorem gl_finrank_of_observability {K : Type*} {n m : Type} [Field K]
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (q ρ : ℕ) (M : Matrix n n K) (P : Matrix m n K)
    (hsize : Fintype.card n = (q + 1) * Fintype.card m + ρ)
    (hfirst : Module.finrank K (unobservableSpace M P (q + 1)) = ρ)
    (hnext : Module.finrank K (unobservableSpace M P (q + 2)) = 0) :
    Module.finrank K (glStabilizerSpace M P) = ρ * (Fintype.card m - ρ) := by
  induction q generalizing n with
  | zero =>
    have hP := surjective_of_observabilityMap M P 0
      (observabilityMap_surjective_of_finrank M P 1 (by rw [hfirst]; omega))
    obtain ⟨D, B, hd, ho⟩ := gl_observability_reduction M P hP
    have hk : Module.finrank K (LinearMap.ker (Matrix.toLin' B)) = 0 := by
      have h := (ho 1).symm.trans hnext
      simpa [unobservableSpace] using h
    have hB : Function.Injective B.mulVec :=
      LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hk)
    rw [hd, gl_base_finrank_of_injective D B hB]
    have hr : Fintype.card n - Fintype.card m = ρ := by
      simp only [zero_add, one_mul] at hsize
      omega
    simp only [Fintype.card_fin, hr]
  | succ q ih =>
    have hP := surjective_of_observabilityMap M P (q + 1)
      (observabilityMap_surjective_of_finrank M P (q + 2) (by
        rw [hfirst]
        have hq : q + 1 + 1 = q + 2 := by omega
        rw [hq] at hsize
        omega))
    obtain ⟨D, B, hd, ho⟩ := gl_observability_reduction M P hP
    rw [hd]
    apply ih D B
    · simp only [Fintype.card_fin, Nat.add_mul, one_mul] at hsize ⊢
      omega
    · exact (ho (q + 1)).symm.trans hfirst
    · exact (ho (q + 2)).symm.trans hnext

end FD56
