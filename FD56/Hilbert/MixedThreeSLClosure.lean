/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MixedThreeGL
import FD56.Hilbert.FamilySLClosure
import FD56.Hilbert.MixedSLClosure
import FD56.Hilbert.MixedSLHighDegree

/-! The two critical Hilbert values determine the mixed three-block SL list. -/

noncomputable section
namespace FD56
open Matrix Polynomial

theorem generic_mixed_three_sl_minimal_degrees_of_critical {K : Type*} [Field K]
    (u v : ℕ) (hu : 0 < u) (hv : 0 < v)
    (i₀ : Fin (4 * (u + v) + v))
    (hfive : slHilbert
      (genericAffineSquare K (Fin (4 * (u + v) + v)) (Fin (3 * (u + v) + v)))
      (genericAffineRows K (Fin (4 * (u + v) + v)) (Fin (3 * (u + v) + v))) 5 = 0)
    (hsix : slHilbert
      (genericAffineSquare K (Fin (4 * (u + v) + v)) (Fin (3 * (u + v) + v)))
      (genericAffineRows K (Fin (4 * (u + v) + v)) (Fin (3 * (u + v) + v))) 6 =
      u * (u + 3 * v) + (8 - u * v)) :
    let A := u * (u + 3 * v)
    let B := u ^ 2 + u * v + 3 * v ^ 2
    let C := u * v
    let t := 8 - C
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (4 * (u + v) + v)) (Fin (3 * (u + v) + v)))
      (genericAffineRows K (Fin (4 * (u + v) + v)) (Fin (3 * (u + v) + v))) i₀)
      (List.replicate (A + t) 6 ++
        List.replicate (B + 9 - 2 * t) 7 ++ List.replicate (C - 8) 8) := by
  let A := u * (u + 3 * v)
  let B := u ^ 2 + u * v + 3 * v ^ 2
  let C := u * v
  let t := 8 - C
  have hcond : 8 ≤ B + 2 * C + 1 := by dsimp [B,C]; nlinarith
  obtain ⟨hm0,hm1⟩ := scalar_correction_multiplicity_identity B C 8 hcond
  have hGL := (hasMinimalKernelDegrees_iff_hilbert _ _).mp
    (generic_mixed_three_gl_minimal_degrees (K := K) u v hu hv)
  have h5 : slHilbert
      (genericAffineSquare K (Fin (4 * (u + v) + v)) (Fin (3 * (u + v) + v)))
      (genericAffineRows K (Fin (4 * (u + v) + v)) (Fin (3 * (u + v) + v))) 5 =
      Module.finrank (AffineCoefficientField K
        (MatrixParameters (Fin (4 * (u + v) + v)) (Fin (3 * (u + v) + v))))
        (polynomialKernelAtDegree (glEquationMatrix
          (genericAffineSquare K (Fin (4 * (u + v) + v)) (Fin (3 * (u + v) + v)))
          (genericAffineRows K (Fin (4 * (u + v) + v)) (Fin (3 * (u + v) + v)))) 5) := by
    rw [hfive, hGL 5]
    simp
  change HasMinimalKernelDegrees _
    (List.replicate (A+t) 6 ++ List.replicate (B+9-2*t) 7 ++ List.replicate (C-8) 8)
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [← slHilbert_eq_matrix_kernel _ _ i₀]
  simp only [List.map_append, List.map_replicate, List.sum_append,
    List.sum_replicate, smul_eq_mul]
  by_cases hd : d ≤ 5
  · rw [generic_middle_slHilbert_eq_gl_below_of_eq_at_degree i₀
      (by simp; omega) (by simp; omega) 5 d hd h5, hGL d]
    have h6 : d + 1 - 6 = 0 := by omega
    have h7 : d + 1 - 7 = 0 := by omega
    have h8 : d + 1 - 8 = 0 := by omega
    simp [h6,h7,h8]
  · by_cases he : d = 6
    · subst d
      rw [hsix]
      simp only [Nat.reduceAdd, Nat.reduceSub, mul_one, mul_zero, add_zero]
      rfl
    · rw [generic_mixed_three_slHilbert_high u v hu (by simp)
        (by simp only [Fintype.card_fin]; ring) i₀ d (by omega), hGL d]
      simp only [List.map_append, List.map_replicate, List.sum_append,
        List.sum_replicate, smul_eq_mul]
      change A * (d+1-6) + B * (d+1-7) + C * (d+1-8) + (d+2) = _
      have h6 : d+1-6 = d-7+2 := by omega
      have h7 : d+1-7 = d-7+1 := by omega
      have h8 : d+1-8 = d-7 := by omega
      have hD : d+2 = d-7+9 := by omega
      rw [h6,h7,h8,hD]
      change 2*t+(B+9-2*t) = B+9 at hm0
      change t+(B+9-2*t)+(C-8) = B+C+1 at hm1
      nlinarith only [hm0, congrArg (fun z => z * (d-7)) hm1]

end FD56
