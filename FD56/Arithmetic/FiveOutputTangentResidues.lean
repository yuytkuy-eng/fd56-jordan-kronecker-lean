/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic

/-! Residue classes and explicit weights for the divisible five-output family. -/

namespace FD56

private theorem residue_check : ∀ r : Fin 28,
    (5 * r.val ^ 2 + 9 * r.val + 4) % 28 = 0 ↔
      r.val = 16 ∨ r.val = 20 ∨ r.val = 23 ∨ r.val = 27 := by decide

theorem five_output_tangent_weight_divisible_iff (q W : ℕ)
    (hW : 2 * W = 5 * q ^ 2 + 9 * q + 4) :
    14 ∣ W ↔ q % 28 = 16 ∨ q % 28 = 20 ∨ q % 28 = 23 ∨ q % 28 = 27 := by
  have hd : 14 ∣ W ↔ 28 ∣ 5 * q ^ 2 + 9 * q + 4 := by
    rw [← hW]
    exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 2)).symm
  have hm : (5 * q ^ 2 + 9 * q + 4) % 28 =
      (5 * (q % 28) ^ 2 + 9 * (q % 28) + 4) % 28 := by
    simp only [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, Nat.mod_mod]
  rw [hd, Nat.dvd_iff_mod_eq_zero, hm]
  exact residue_check ⟨q % 28, Nat.mod_lt q (by decide)⟩

theorem five_output_tangent_residue_weight (t c h W : ℕ)
    (hc : (c = 16 ∧ h = 51) ∨ (c = 20 ∧ h = 78) ∨
      (c = 23 ∧ h = 102) ∨ (c = 27 ∧ h = 139))
    (hW : 2 * W = 5 * (28 * t + c) ^ 2 + 9 * (28 * t + c) + 4) :
    W = 14 * (140 * t ^ 2 + (10 * c + 9) * t + h) := by
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    nlinarith

theorem five_output_tangent_positive_multiplier (q W : ℕ)
    (hW : 2 * W = 5 * q ^ 2 + 9 * q + 4)
    (hq : q % 28 = 16 ∨ q % 28 = 20 ∨ q % 28 = 23 ∨ q % 28 = 27) :
    ∃ h : ℕ, 0 < h ∧ W = 14 * h := by
  obtain ⟨h, hh⟩ := (five_output_tangent_weight_divisible_iff q W hW).mpr hq
  exact ⟨h, by omega, hh⟩

end FD56
