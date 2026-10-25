/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.NonzeroMaximalMinor

/-! Vanishing maximal minors give a kernel vector with one coordinate equal to one. -/

namespace FD56
open Matrix
variable {K a n : Type*} [Field K] [Fintype a] [Fintype n] [DecidableEq a] [DecidableEq n]

theorem nonzero_kernel_of_zero_maximal_minors (A : Matrix a n K)
    (h : ∀ r : n → a, (A.submatrix r id).det = 0) :
    ∃ v : n → K, A *ᵥ v = 0 ∧ v ≠ 0 := by
  have hn : ¬ Function.Injective A.mulVec := by
    intro hi
    obtain ⟨r, hr⟩ := exists_nonzero_maximal_minor_of_injective A hi
    exact hr (h r)
  have hk : LinearMap.ker (Matrix.toLin' A) ≠ ⊥ := by
    intro hk
    exact hn (LinearMap.ker_eq_bot.mp hk)
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  exact ⟨v, hv, hv0⟩

theorem normalized_kernel_of_zero_maximal_minors (A : Matrix a n K)
    (h : ∀ r : n → a, (A.submatrix r id).det = 0) :
    ∃ (i : n) (v : n → K), A *ᵥ v = 0 ∧ v i = 1 := by
  obtain ⟨v, hv, hv0⟩ := nonzero_kernel_of_zero_maximal_minors A h
  have hex : ∃ i, v i ≠ 0 := by
    by_contra hn
    apply hv0
    funext i
    simpa using not_exists.mp hn i
  obtain ⟨i, hi⟩ := hex
  refine ⟨i, (v i)⁻¹ • v, ?_, ?_⟩
  · have hh := map_smul (Matrix.toLin' A) (v i)⁻¹ v
    change A *ᵥ ((v i)⁻¹ • v) = (v i)⁻¹ • (A *ᵥ v) at hh
    rw [hh, hv, smul_zero]
  · simpa only [Pi.smul_apply, smul_eq_mul] using inv_mul_cancel₀ hi

end FD56
