/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.UniformSmallGL
import FD56.Hilbert.UniformSLHighDegree
import FD56.Hilbert.UniformThreeSLRealization
import FD56.Hilbert.GenericKernelBound
import FD56.Hilbert.FamilySLClosure
import FD56.Hilbert.UniformGeneralSLClassification

/-! Actual generic SL minimal degrees in dimensions (4r,3r), r at least three. -/

noncomputable section
namespace FD56
open Matrix Polynomial

theorem generic_uniform_three_sl_minimal_degrees {K : Type*} [Field K]
    (r : ℕ) (hr : 3 ≤ r) (i₀ : Fin (4 * r)) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (4 * r)) (Fin (3 * r)))
      (genericAffineRows K (Fin (4 * r)) (Fin (3 * r))) i₀)
      (List.replicate (r ^ 2 + 8) 6 ++ List.replicate (r ^ 2 - 7) 7) := by
  have hGL := (hasMinimalKernelDegrees_iff_hilbert _ _).mp
    (generic_uniform_three_gl_minimal_degrees (K := K) r (by omega))
  have h5 : slHilbert (genericAffineSquare K (Fin (4 * r)) (Fin (3 * r)))
      (genericAffineRows K (Fin (4 * r)) (Fin (3 * r))) 5 =
      Module.finrank (AffineCoefficientField K (MatrixParameters (Fin (4 * r)) (Fin (3 * r))))
        (polynomialKernelAtDegree (glEquationMatrix
          (genericAffineSquare K (Fin (4 * r)) (Fin (3 * r)))
          (genericAffineRows K (Fin (4 * r)) (Fin (3 * r)))) 5) := by
    rw [generic_uniform_three_slHilbert_five r hr, hGL 5]
    simp
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
    simp [h6, h7]
  · rw [generic_uniform_three_slHilbert_high r (by omega)
      (by simp) (by simp) i₀ d (by omega), hGL d]
    simp only [List.map_append, List.sum_append, List.map_replicate, List.sum_replicate, smul_eq_mul]
    have h6 : d + 1 - 6 = d - 6 + 1 := by omega
    have h7 : d + 1 - 7 = d - 6 := by omega
    have hD : d + 2 = d - 6 + 8 := by omega
    have hr2 : 9 ≤ r ^ 2 := by nlinarith
    have hsub : r ^ 2 - 7 + 7 = r ^ 2 := Nat.sub_add_cancel (by omega)
    rw [h6, h7, hD]
    nlinarith [congrArg (fun z => z * (d - 6)) hsub]

theorem generic_uniform_three_slHilbert {K : Type*} [Field K]
    (r : ℕ) (hr : 3 ≤ r) (d : ℕ) :
    slHilbert (genericAffineSquare K (Fin (4 * r)) (Fin (3 * r)))
      (genericAffineRows K (Fin (4 * r)) (Fin (3 * r))) d =
      (r ^ 2 + 8) * (d - 5) + (r ^ 2 - 7) * (d - 6) := by
  let i₀ : Fin (4 * r) := ⟨0, by omega⟩
  rw [slHilbert_eq_matrix_kernel _ _ i₀,
    (hasMinimalKernelDegrees_iff_hilbert _ _).mp
      (generic_uniform_three_sl_minimal_degrees (K := K) r hr i₀) d]
  simp only [List.map_append, List.map_replicate, List.sum_append,
    List.sum_replicate, smul_eq_mul]
  congr 2

theorem generic_uniform_three_two_sl_minimal_degrees_of_five {K : Type*} [Field K]
    (i₀ : Fin 8)
    (hfive : slHilbert (genericAffineSquare K (Fin 8) (Fin 6))
      (genericAffineRows K (Fin 8) (Fin 6)) 5 = 3) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin 8) (Fin 6))
      (genericAffineRows K (Fin 8) (Fin 6)) i₀)
      (List.replicate 3 5 ++ List.replicate 6 6) := by
  have hGL := (hasMinimalKernelDegrees_iff_hilbert _ _).mp
    (generic_uniform_three_gl_minimal_degrees (K := K) 2 (by decide))
  have hfour : slHilbert (genericAffineSquare K (Fin 8) (Fin 6))
      (genericAffineRows K (Fin 8) (Fin 6)) 4 = 0 := by
    simpa using generic_uniform_slHilbert_critical (K := K) 3 2 (by decide) (by decide)
  have h4 : slHilbert (genericAffineSquare K (Fin 8) (Fin 6))
      (genericAffineRows K (Fin 8) (Fin 6)) 4 =
      Module.finrank (AffineCoefficientField K (MatrixParameters (Fin 8) (Fin 6)))
        (polynomialKernelAtDegree (glEquationMatrix
          (genericAffineSquare K (Fin 8) (Fin 6))
          (genericAffineRows K (Fin 8) (Fin 6))) 4) := by
    rw [hfour, hGL 4]
    simp
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [← slHilbert_eq_matrix_kernel _ _ i₀]
  simp only [List.map_append, List.map_replicate, List.sum_append,
    List.sum_replicate, smul_eq_mul]
  by_cases hd : d ≤ 4
  · rw [generic_middle_slHilbert_eq_gl_below_of_eq_at_degree i₀
      (by decide) (by decide) 4 d hd h4, hGL d]
    have h5 : d + 1 - 5 = 0 := by omega
    have h6 : d + 1 - 6 = 0 := by omega
    have h7 : d + 1 - 7 = 0 := by omega
    simp [h5, h6, h7]
  · by_cases he : d = 5
    · subst d
      simpa using hfive
    · rw [generic_uniform_three_slHilbert_high 2 (by decide)
        (by simp) (by simp) i₀ d (by omega), hGL d]
      simp only [List.map_append, List.sum_append, List.map_replicate,
        List.sum_replicate, smul_eq_mul]
      norm_num
      omega

theorem generic_uniform_three_two_sl_minimal_degrees {K : Type*} [Field K]
    (i₀ : Fin 8) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin 8) (Fin 6))
      (genericAffineRows K (Fin 8) (Fin 6)) i₀)
      (List.replicate 3 5 ++ List.replicate 6 6) :=
  generic_uniform_three_two_sl_minimal_degrees_of_five i₀
    (generic_uniform_three_two_slHilbert_five (K := K))

end FD56
