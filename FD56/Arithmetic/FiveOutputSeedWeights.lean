/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic

/-! Eight finite seed weights cover both five-output interior weight
sequences from depth two onward, modulo the proved splice increment. -/

namespace FD56

private theorem residue_two_check : ∀ r : Fin 28,
    (5*r.val^2+9*r.val+4)%28/2 ∈ ([0,2,3,4,7,9,10,11] : List ℕ) := by decide

private theorem residue_three_check : ∀ r : Fin 28,
    (5*r.val^2+11*r.val+6)%28/2 ∈ ([0,2,3,4,7,9,10,11] : List ℕ) := by decide

private theorem seed_of_remainder (W : ℕ) (hW : 14≤W)
    (hres : W%14 ∈ ([0,2,3,4,7,9,10,11] : List ℕ)) :
    ∃ s ∈ ([14,16,17,18,21,23,24,25] : List ℕ), ∃ t : ℕ, W=s+14*t := by
  refine ⟨14+W%14,?_,W/14-1,?_⟩
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hres ⊢
    omega
  · omega

theorem five_output_tangent_seed_weight (q W : ℕ) (hq : 2≤q)
    (hW : 2*W=5*q^2+9*q+4) :
    ∃ s ∈ ([14,16,17,18,21,23,24,25] : List ℕ), ∃ t : ℕ, W=s+14*t := by
  have hlarge : 14≤W := by nlinarith
  have hm : (5*q^2+9*q+4)%28=(5*(q%28)^2+9*(q%28)+4)%28 := by
    simp only [Nat.add_mod,Nat.mul_mod,Nat.pow_mod,Nat.mod_mod]
  have hx := congrArg (fun n : ℕ => n%28) hW
  change (2*W)%(2*14)=(5*q^2+9*q+4)%28 at hx
  rw [Nat.mul_mod_mul_left,hm] at hx
  have hr : W%14=(5*(q%28)^2+9*(q%28)+4)%28/2 := by omega
  apply seed_of_remainder W hlarge
  rw [hr]
  exact residue_two_check ⟨q%28,Nat.mod_lt q (by decide)⟩

theorem five_output_corank_two_tangent_seed_weight (q W : ℕ) (hq : 2≤q)
    (hW : 2*W=5*q^2+11*q+6) :
    ∃ s ∈ ([14,16,17,18,21,23,24,25] : List ℕ), ∃ t : ℕ, W=s+14*t := by
  have hlarge : 14≤W := by nlinarith
  have hm : (5*q^2+11*q+6)%28=(5*(q%28)^2+11*(q%28)+6)%28 := by
    simp only [Nat.add_mod,Nat.mul_mod,Nat.pow_mod,Nat.mod_mod]
  have hx := congrArg (fun n : ℕ => n%28) hW
  change (2*W)%(2*14)=(5*q^2+11*q+6)%28 at hx
  rw [Nat.mul_mod_mul_left,hm] at hx
  have hr : W%14=(5*(q%28)^2+11*(q%28)+6)%28/2 := by omega
  apply seed_of_remainder W hlarge
  rw [hr]
  exact residue_three_check ⟨q%28,Nat.mod_lt q (by decide)⟩

end FD56
