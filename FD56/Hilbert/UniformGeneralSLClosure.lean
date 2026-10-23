/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.UniformGeneralGL
import FD56.Hilbert.UniformSL

/-! The critical bounded dimension determines every uniform SL minimal degree. -/

noncomputable section
namespace FD56
open Matrix Polynomial

theorem uniform_sl_multiplicity_identity (a r : ℕ) (ha : 4 ≤ a) (hr : 0 < r) :
    let t := a + 3 - 3 * r ^ 2
    let u := (a - 4) * r ^ 2 + a + 4 - 2 * t
    let v := 3 * r ^ 2 - (a + 3)
    2 * t + u = (a - 4) * r ^ 2 + a + 4 ∧
      t + u + v = (a - 4) * r ^ 2 + 3 * r ^ 2 + 1 := by
  dsimp
  have hr2 : 1 ≤ r ^ 2 := by nlinarith
  have ha4 := Nat.sub_add_cancel ha
  have hA : a - 4 ≤ (a - 4) * r ^ 2 := by nlinarith
  by_cases hb : a + 3 ≤ 3 * r ^ 2
  · have ht : a + 3 - 3 * r ^ 2 = 0 := Nat.sub_eq_zero_of_le hb
    have hv := Nat.sub_add_cancel hb
    constructor
    · rw [ht]
      simp
    · rw [ht]
      simp only [mul_zero, Nat.sub_zero, zero_add]
      omega
  · have ht := Nat.sub_add_cancel (show 3 * r ^ 2 ≤ a + 3 by omega)
    have hv : 3 * r ^ 2 - (a + 3) = 0 := by omega
    have hu : 2 * (a + 3 - 3 * r ^ 2) ≤ (a - 4) * r ^ 2 + a + 4 := by omega
    have hh := Nat.sub_add_cancel hu
    rw [hv]
    constructor <;> omega

theorem generic_uniform_sl_minimal_degrees_of_critical {K : Type*} [Field K]
    (a r : ℕ) (ha : 4 ≤ a) (hr : 0 < r) (i₀ : Fin ((a + 1) * r))
    (hcritical : slHilbert
      (genericAffineSquare K (Fin ((a + 1) * r)) (Fin (a * r)))
      (genericAffineRows K (Fin ((a + 1) * r)) (Fin (a * r))) (a + 1) =
      a + 3 - 3 * r ^ 2) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin ((a + 1) * r)) (Fin (a * r)))
      (genericAffineRows K (Fin ((a + 1) * r)) (Fin (a * r))) i₀)
      (List.replicate (a + 3 - 3 * r ^ 2) (a + 1) ++
        List.replicate ((a - 4) * r ^ 2 + a + 4 - 2 * (a + 3 - 3 * r ^ 2)) (a + 2) ++
        List.replicate (3 * r ^ 2 - (a + 3)) (a + 3)) := by
  have hGL := (hasMinimalKernelDegrees_iff_hilbert _ _).mp
    (generic_uniform_gl_minimal_degrees (K := K) a r ha hr)
  obtain ⟨hm0, hm1⟩ := uniform_sl_multiplicity_identity a r ha hr
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [← slHilbert_eq_matrix_kernel _ _ i₀]
  simp only [List.map_append, List.map_replicate, List.sum_append,
    List.sum_replicate, smul_eq_mul]
  by_cases hd : d ≤ a
  · rw [generic_uniform_slHilbert_low a r (by omega) hr (by simp) (by simp) i₀ d hd]
    have h1 : d + 1 - (a + 1) = 0 := by omega
    have h2 : d + 1 - (a + 2) = 0 := by omega
    have h3 : d + 1 - (a + 3) = 0 := by omega
    simp [h1, h2, h3]
  · by_cases hc : d = a + 1
    · subst d
      rw [hcritical]
      have h1 : a + 1 + 1 - (a + 1) = 1 := by omega
      have h2 : a + 1 + 1 - (a + 2) = 0 := by omega
      have h3 : a + 1 + 1 - (a + 3) = 0 := by omega
      simp [h1, h2, h3]
    · have hd' : a + 2 ≤ d := by omega
      rw [generic_uniform_slHilbert_high a r ha hr (by simp) (by simp) i₀ d hd', hGL d]
      simp only [List.map_append, List.map_replicate, List.sum_append,
        List.sum_replicate, smul_eq_mul]
      have h1 : d + 1 - (a + 1) = (d - (a + 2)) + 2 := by omega
      have h2 : d + 1 - (a + 2) = (d - (a + 2)) + 1 := by omega
      have h3 : d + 1 - (a + 3) = d - (a + 2) := by omega
      have hD : d + 2 = (d - (a + 2)) + (a + 4) := by omega
      rw [h1, h2, h3, hD]
      nlinarith [congrArg (fun z => z * (d - (a + 2))) hm1]

end FD56
