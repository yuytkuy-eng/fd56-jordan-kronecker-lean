/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MixedGL
import FD56.Hilbert.MixedSLDegrees

/-! The mixed critical scalar dimension determines the full SL degree list. -/

noncomputable section
namespace FD56
open Matrix Polynomial

theorem scalar_correction_multiplicity_identity (B C s : ℕ) (h : s ≤ B + 2 * C + 1) :
    2 * (s - C) + (B + s + 1 - 2 * (s - C)) = B + s + 1 ∧
      (s - C) + (B + s + 1 - 2 * (s - C)) + (C - s) = B + C + 1 := by
  by_cases hs : s ≤ C
  · have ht : s - C = 0 := Nat.sub_eq_zero_of_le hs
    have hh := Nat.sub_add_cancel hs
    constructor
    · simp [ht]
    · rw [ht]
      simp only [mul_zero, Nat.sub_zero, zero_add]
      omega
  · have ht := Nat.sub_add_cancel (show C ≤ s by omega)
    have hv : C - s = 0 := by omega
    have hp : 2 * (s - C) ≤ B + s + 1 := by omega
    have hh := Nat.sub_add_cancel hp
    constructor <;> omega

theorem generic_mixed_sl_minimal_degrees_of_critical {K : Type*} [Field K]
    (a u v : ℕ) (ha : 4 ≤ a) (hu : 0 < u) (hv : 0 < v)
    (i₀ : Fin ((a + 1) * (u + v) + v))
    (hcritical : slHilbert
      (genericAffineSquare K (Fin ((a + 1) * (u + v) + v)) (Fin (a * (u + v) + v)))
      (genericAffineRows K (Fin ((a + 1) * (u + v) + v)) (Fin (a * (u + v) + v)))
      (a + 2) = u * ((a - 4) * (u + v) + v) + (a + 4 - 3 * v * (u + v))) :
    let r := u + v
    let g := (a - 4) * r + v
    let A := u * g
    let B := 3 * u * r + v * g
    let C := 3 * v * r
    let t := a + 4 - C
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin ((a + 1) * r + v)) (Fin (a * r + v)))
      (genericAffineRows K (Fin ((a + 1) * r + v)) (Fin (a * r + v))) i₀)
      (List.replicate (A + t) (a + 2) ++
        List.replicate (B + a + 5 - 2 * t) (a + 3) ++
        List.replicate (C - (a + 4)) (a + 4)) := by
  let r := u + v
  let g := (a - 4) * r + v
  let A := u * g
  let B := 3 * u * r + v * g
  let C := 3 * v * r
  let t := a + 4 - C
  have hr : 2 ≤ r := by dsimp [r]; omega
  have hg : a - 4 ≤ g := by dsimp [g]; nlinarith
  have hB : a - 4 ≤ B := by dsimp [B]; nlinarith
  have hC : 6 ≤ C := by dsimp [C]; nlinarith
  have hcond : a + 4 ≤ B + 2 * C + 1 := by omega
  obtain ⟨hm0, hm1⟩ := scalar_correction_multiplicity_identity B C (a + 4) hcond
  have hGL := (hasMinimalKernelDegrees_iff_hilbert _ _).mp
    (generic_mixed_gl_minimal_degrees (K := K) a u v ha hu hv)
  change HasMinimalKernelDegrees _
    (List.replicate (A + t) (a + 2) ++ List.replicate (B + a + 5 - 2 * t) (a + 3) ++
      List.replicate (C - (a + 4)) (a + 4))
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [← slHilbert_eq_matrix_kernel _ _ i₀]
  simp only [List.map_append, List.map_replicate, List.sum_append,
    List.sum_replicate, smul_eq_mul]
  by_cases hd : d ≤ a + 1
  · rw [generic_mixed_slHilbert_low a u v ha hu hv (by simp)
      (by simp only [Fintype.card_fin]; ring) i₀ d hd, hGL d]
    have h2 : d + 1 - (a + 2) = 0 := by omega
    have h3 : d + 1 - (a + 3) = 0 := by omega
    have h4 : d + 1 - (a + 4) = 0 := by omega
    simp [h2, h3, h4]
  · by_cases he : d = a + 2
    · subst d
      rw [hcritical]
      have h2 : a + 2 + 1 - (a + 2) = 1 := by omega
      have h3 : a + 2 + 1 - (a + 3) = 0 := by omega
      have h4 : a + 2 + 1 - (a + 4) = 0 := by omega
      simp only [h2, h3, h4, mul_one, mul_zero, add_zero]
      rfl
    · rw [generic_mixed_slHilbert_high a u v ha hu (by simp)
        (by simp only [Fintype.card_fin]; ring) i₀ d (by omega), hGL d]
      simp only [List.map_append, List.map_replicate, List.sum_append,
        List.sum_replicate, smul_eq_mul]
      change A * (d + 1 - (a + 2)) + B * (d + 1 - (a + 3)) + C * (d + 1 - (a + 4)) +
        (d + 2) = _
      have h2 : d + 1 - (a + 2) = d - (a + 3) + 2 := by omega
      have h3 : d + 1 - (a + 3) = d - (a + 3) + 1 := by omega
      have h4 : d + 1 - (a + 4) = d - (a + 3) := by omega
      have hD : d + 2 = d - (a + 3) + a + 5 := by omega
      rw [h2, h3, h4, hD]
      have hp : B + a + 5 = B + (a + 4) + 1 := by omega
      rw [hp]
      change 2 * t + (B + (a + 4) + 1 - 2 * t) = _ at hm0
      change t + (B + (a + 4) + 1 - 2 * t) + (C - (a + 4)) = _ at hm1
      nlinarith only [hm0, congrArg (fun z => z * (d - (a + 3))) hm1]

end FD56
