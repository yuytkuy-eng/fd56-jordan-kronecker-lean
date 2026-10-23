/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.UniformClassification
import FD56.Hilbert.AdjacentDegrees

/-! Balanced form of the proved uniform SL degree lists. -/

noncomputable section
namespace FD56
open Matrix Polynomial

theorem generic_uniform_large_sl_balanced {K : Type*} [Field K]
    (a r : ℕ) (ha : 4 ≤ a) (hr : 0 < r) (i₀ : Fin ((a + 1) * r)) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin ((a + 1) * r)) (Fin (a * r)))
      (genericAffineRows K (Fin ((a + 1) * r)) (Fin (a * r))) i₀)
      (balancedDegreeList ((a ^ 2 + a + 1) * r ^ 2 - 1) ((a - 1) * r ^ 2 + 1)) := by
  have hg := generic_uniform_sl_minimal_degrees (K := K) a r ha hr i₀
  have hr2 : 1 ≤ r ^ 2 := by nlinarith
  have ha4 := Nat.sub_add_cancel ha
  have ha1 := Nat.sub_add_cancel (show 1 ≤ a by omega)
  obtain ⟨hm0, hm1⟩ := uniform_sl_multiplicity_identity a r ha hr
  have hS : 1 ≤ (a ^ 2 + a + 1) * r ^ 2 := by nlinarith
  by_cases hb : a + 3 ≤ 3 * r ^ 2
  · have ht : a + 3 - 3 * r ^ 2 = 0 := Nat.sub_eq_zero_of_le hb
    have hv := Nat.sub_add_cancel hb
    simp only [ht, mul_zero, Nat.sub_zero, List.replicate_zero, List.nil_append] at hg
    have hc : ((a - 4) * r ^ 2 + a + 4) + (3 * r ^ 2 - (a + 3)) =
        (a - 1) * r ^ 2 + 1 := by
      nlinarith only [hv, congrArg (fun z => z * r ^ 2) ha4,
        congrArg (fun z => z * r ^ 2) ha1]
    have hs : (a + 2) * (((a - 4) * r ^ 2 + a + 4) + (3 * r ^ 2 - (a + 3))) +
        (3 * r ^ 2 - (a + 3)) = (a ^ 2 + a + 1) * r ^ 2 - 1 := by
      rw [hc]
      have he : (a + 2) * ((a - 1) * r ^ 2 + 1) + (3 * r ^ 2 - (a + 3)) + 1 =
          (a ^ 2 + a + 1) * r ^ 2 := by
        nlinarith only [hv, congrArg (fun z => z * ((a + 2) * r ^ 2)) ha1]
      omega
    have hh := hasMinimalKernelDegrees_balanced_of_adjacent _
      ((a - 4) * r ^ 2 + a + 4) (3 * r ^ 2 - (a + 3)) (a + 2)
      (by rw [hc]; omega) (by simpa only [Nat.add_assoc] using hg)
    rw [hs, hc] at hh
    exact hh
  · have hv : 3 * r ^ 2 - (a + 3) = 0 := by omega
    have ht := Nat.sub_add_cancel (show 3 * r ^ 2 ≤ a + 3 by omega)
    simp only [hv, List.replicate_zero, List.append_nil] at hg
    simp only [hv, add_zero] at hm1
    have hc : (a + 3 - 3 * r ^ 2) +
        ((a - 4) * r ^ 2 + a + 4 - 2 * (a + 3 - 3 * r ^ 2)) =
        (a - 1) * r ^ 2 + 1 := by
      nlinarith only [hm1, congrArg (fun z => z * r ^ 2) ha4,
        congrArg (fun z => z * r ^ 2) ha1]
    have hs : (a + 1) * ((a + 3 - 3 * r ^ 2) +
        ((a - 4) * r ^ 2 + a + 4 - 2 * (a + 3 - 3 * r ^ 2))) +
        ((a - 4) * r ^ 2 + a + 4 - 2 * (a + 3 - 3 * r ^ 2)) =
        (a ^ 2 + a + 1) * r ^ 2 - 1 := by
      rw [hc]
      have he : (a + 1) * ((a - 1) * r ^ 2 + 1) +
          ((a - 4) * r ^ 2 + a + 4 - 2 * (a + 3 - 3 * r ^ 2)) + 1 =
          (a ^ 2 + a + 1) * r ^ 2 := by
        nlinarith only [hm0, ht, congrArg (fun z => z * r ^ 2) ha4,
          congrArg (fun z => z * ((a + 1) * r ^ 2)) ha1]
      omega
    have hh := hasMinimalKernelDegrees_balanced_of_adjacent _
      (a + 3 - 3 * r ^ 2) ((a - 4) * r ^ 2 + a + 4 - 2 * (a + 3 - 3 * r ^ 2))
      (a + 1) (by rw [hc]; omega) (by simpa only [Nat.add_assoc] using hg)
    rw [hs, hc] at hh
    exact hh

theorem generic_uniform_two_sl_balanced {K : Type*} [Field K]
    (r : ℕ) (hr : 0 < r) (i₀ : Fin (3 * r)) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (3 * r)) (Fin (2 * r)))
      (genericAffineRows K (Fin (3 * r)) (Fin (2 * r))) i₀)
      (balancedDegreeList (7 * r ^ 2 - 1) (1 * r ^ 2 + 1)) := by
  by_cases hr1 : r = 1
  · subst r
    have h := generic_one_more_column_sl_minimal_degrees (K := K)
      (n := Fin 3) (m := Fin 2) i₀ (by decide) (by decide)
    simpa [balancedDegreeList] using h
  · by_cases hr2 : r = 2
    · subst r
      have h := hasMinimalKernelDegrees_balanced_of_adjacent _ 3 2 5 (by decide)
        (generic_uniform_two_two_sl_minimal_degrees (K := K) i₀)
      norm_num at h ⊢
      exact h
    · have hr3 : 3 ≤ r := by omega
      have hr9 : 9 ≤ r ^ 2 := by nlinarith
      have ht := Nat.sub_add_cancel (show 7 ≤ r ^ 2 by omega)
      have hc : (8) + (r ^ 2 - 7) = 1 * r ^ 2 + 1 := by omega
      have hs : 6 * ((8) + (r ^ 2 - 7)) + (r ^ 2 - 7) = 7 * r ^ 2 - 1 := by omega
      have h := hasMinimalKernelDegrees_balanced_of_adjacent _ (8) (r ^ 2 - 7) 6
        (by omega) (generic_uniform_two_sl_minimal_degrees (K := K) r hr3 i₀)
      rw [hs, hc] at h
      exact h

theorem generic_uniform_three_sl_balanced {K : Type*} [Field K]
    (r : ℕ) (hr : 0 < r) (i₀ : Fin (4 * r)) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (4 * r)) (Fin (3 * r)))
      (genericAffineRows K (Fin (4 * r)) (Fin (3 * r))) i₀)
      (balancedDegreeList (13 * r ^ 2 - 1) (2 * r ^ 2 + 1)) := by
  by_cases hr1 : r = 1
  · subst r
    have h := generic_one_more_column_sl_minimal_degrees (K := K)
      (n := Fin 4) (m := Fin 3) i₀ (by decide) (by decide)
    simpa [balancedDegreeList] using h
  · by_cases hr2 : r = 2
    · subst r
      have h := hasMinimalKernelDegrees_balanced_of_adjacent _ 3 6 5 (by decide)
        (generic_uniform_three_two_sl_minimal_degrees (K := K) i₀)
      norm_num at h ⊢
      exact h
    · have hr3 : 3 ≤ r := by omega
      have hr9 : 9 ≤ r ^ 2 := by nlinarith
      have ht := Nat.sub_add_cancel (show 7 ≤ r ^ 2 by omega)
      have hc : (r ^ 2 + 8) + (r ^ 2 - 7) = 2 * r ^ 2 + 1 := by omega
      have hs : 6 * ((r ^ 2 + 8) + (r ^ 2 - 7)) + (r ^ 2 - 7) = 13 * r ^ 2 - 1 := by omega
      have h := hasMinimalKernelDegrees_balanced_of_adjacent _ (r ^ 2 + 8) (r ^ 2 - 7) 6
        (by omega) (generic_uniform_three_sl_minimal_degrees (K := K) r hr3 i₀)
      rw [hs, hc] at h
      exact h

theorem generic_uniform_middle_sl_balanced {K : Type*} [Field K]
    (a r : ℕ) (ha : 2 ≤ a) (hr : 0 < r) (i₀ : Fin ((a + 1) * r)) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin ((a + 1) * r)) (Fin (a * r)))
      (genericAffineRows K (Fin ((a + 1) * r)) (Fin (a * r))) i₀)
      (balancedDegreeList ((a ^ 2 + a + 1) * r ^ 2 - 1) ((a - 1) * r ^ 2 + 1)) := by
  by_cases ha2 : a = 2
  · subst a
    simpa using generic_uniform_two_sl_balanced (K := K) r hr i₀
  · by_cases ha3 : a = 3
    · subst a
      simpa using generic_uniform_three_sl_balanced (K := K) r hr i₀
    · exact generic_uniform_large_sl_balanced a r (by omega) hr i₀

end FD56
