/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic

/-! Three finite weights cover both six-output two-column interior
sequences at every positive depth, modulo the short splice increment. -/

namespace FD56

private theorem seed_of_even_weight (W h : ℕ) (hlarge : 6≤W) (heven : W=2*h) :
    ∃ s ∈ ([6,8,10] : List ℕ), ∃ t : ℕ, W=s+6*t := by
  refine ⟨6+W%6,?_,W/6-1,?_⟩
  · simp only [List.mem_cons,List.not_mem_nil,or_false]
    omega
  · omega

theorem six_output_tangent_seed_weight (q W : ℕ) (hq : 0<q)
    (hW : W=3*q^2+5*q+2) :
    ∃ s ∈ ([6,8,10] : List ℕ), ∃ t : ℕ, W=s+6*t := by
  obtain ⟨h,hh⟩ := Nat.even_mul_succ_self q
  have he : W=2*(3*h+q+1) := by nlinarith
  exact seed_of_even_weight W (3*h+q+1) (by nlinarith) he

theorem six_output_corank_two_tangent_seed_weight (q W : ℕ) (hq : 0<q)
    (hW : W=3*q^2+7*q+4) :
    ∃ s ∈ ([6,8,10] : List ℕ), ∃ t : ℕ, W=s+6*t := by
  obtain ⟨h,hh⟩ := Nat.even_mul_succ_self q
  have he : W=2*(3*h+2*q+2) := by nlinarith
  exact seed_of_even_weight W (3*h+2*q+2) (by nlinarith) he

end FD56
