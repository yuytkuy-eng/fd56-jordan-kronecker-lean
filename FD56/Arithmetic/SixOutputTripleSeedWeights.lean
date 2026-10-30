/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic

/-! The three-column degree sequence uses only three classes modulo the
degree-five splice increment. -/

namespace FD56

theorem six_output_triple_tangent_seed_degree (q : ℕ) (hq : 0<q) :
    ∃ s ∈ ([1,4,5] : List ℕ), ∃ t : ℕ, (q+1)^2=s+5*t := by
  have hlarge : 4≤(q+1)^2 := by nlinarith
  have hmod : (q+1)^2%5=0 ∨ (q+1)^2%5=1 ∨ (q+1)^2%5=4 := by
    rw [Nat.pow_mod]
    have hr := Nat.mod_lt (q+1) (by omega : 0<5)
    interval_cases hrem : (q+1)%5 <;> norm_num
  rcases hmod with hzero|hone|hfour
  · exact ⟨5,by simp,(q+1)^2/5-1,by omega⟩
  · exact ⟨1,by simp,(q+1)^2/5,by omega⟩
  · exact ⟨4,by simp,(q+1)^2/5,by omega⟩

end FD56
