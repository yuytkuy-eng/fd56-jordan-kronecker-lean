/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic

/-! Divisible weights for the five-output corank-two tangent criterion. -/

namespace FD56

private theorem corank_two_residue_check : ∀ r : Fin 28,
    (5 * r.val ^ 2 + 11 * r.val + 6) % 28 = 0 ↔
      r.val = 3 ∨ r.val = 6 ∨ r.val = 10 ∨ r.val = 27 := by decide

theorem five_output_corank_two_tangent_weight_divisible_iff (q W : ℕ)
    (hW : 2 * W = 5 * q ^ 2 + 11 * q + 6) :
    14 ∣ W ↔ q % 28 = 3 ∨ q % 28 = 6 ∨ q % 28 = 10 ∨ q % 28 = 27 := by
  have hd : 14 ∣ W ↔ 28 ∣ 5 * q ^ 2 + 11 * q + 6 := by
    rw [← hW]
    exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 2)).symm
  have hm : (5 * q ^ 2 + 11 * q + 6) % 28 =
      (5 * (q % 28) ^ 2 + 11 * (q % 28) + 6) % 28 := by
    simp only [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, Nat.mod_mod]
  rw [hd, Nat.dvd_iff_mod_eq_zero, hm]
  exact corank_two_residue_check ⟨q % 28, Nat.mod_lt q (by decide)⟩

theorem five_output_corank_two_tangent_residue_weight (t c h W : ℕ)
    (hc : (c = 3 ∧ h = 3) ∨ (c = 6 ∧ h = 9) ∨
      (c = 10 ∧ h = 22) ∨ (c = 27 ∧ h = 141))
    (hW : 2 * W = 5 * (28 * t + c) ^ 2 + 11 * (28 * t + c) + 6) :
    W = 14 * (140 * t ^ 2 + (10 * c + 11) * t + h) := by
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    nlinarith

theorem five_output_corank_two_tangent_positive_multiplier (q W : ℕ)
    (hW : 2 * W = 5 * q ^ 2 + 11 * q + 6)
    (hq : q % 28 = 3 ∨ q % 28 = 6 ∨ q % 28 = 10 ∨ q % 28 = 27) :
    ∃ h : ℕ, 0 < h ∧ W = 14 * h := by
  obtain ⟨h, hh⟩ := (five_output_corank_two_tangent_weight_divisible_iff q W hW).mpr hq
  exact ⟨h, by omega, hh⟩

end FD56
