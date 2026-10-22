/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.UniformGL
import FD56.Hilbert.UniformSL
import FD56.Hilbert.UniformSLRealization
import FD56.Hilbert.GenericKernelBound
import FD56.Hilbert.FamilySLClosure

/-! Actual generic SL minimal degrees in dimensions (5r,4r), r at least two. -/

noncomputable section
namespace FD56
open Matrix Polynomial

theorem generic_uniform_four_slHilbert_five {K : Type*} [Field K]
    (r : ℕ) (hr : 2 ≤ r) :
    slHilbert (genericAffineSquare K (Fin (5 * r)) (Fin (4 * r)))
      (genericAffineRows K (Fin (5 * r)) (Fin (4 * r))) 5 = 0 := by
  obtain ⟨M, P, hM, hP, hH⟩ := exists_uniform_sl_degree_five_witness (K := K) r hr
  have hb := generic_slHilbert_le_witness M P hM hP (⟨0, by omega⟩ : Fin (5 * r)) 5
  exact Nat.eq_zero_of_le_zero (hb.trans_eq hH)

theorem generic_uniform_four_sl_minimal_degrees {K : Type*} [Field K]
    (r : ℕ) (hr : 2 ≤ r) (i₀ : Fin (5 * r)) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (5 * r)) (Fin (4 * r)))
      (genericAffineRows K (Fin (5 * r)) (Fin (4 * r))) i₀)
      (List.replicate 8 6 ++ List.replicate (3 * r ^ 2 - 7) 7) := by
  have hGL := (hasMinimalKernelDegrees_iff_hilbert _ _).mp
    (generic_uniform_four_gl_minimal_degrees (K := K) r (by omega))
  have h5 : slHilbert (genericAffineSquare K (Fin (5 * r)) (Fin (4 * r)))
      (genericAffineRows K (Fin (5 * r)) (Fin (4 * r))) 5 =
      Module.finrank (AffineCoefficientField K (MatrixParameters (Fin (5 * r)) (Fin (4 * r))))
        (polynomialKernelAtDegree (glEquationMatrix
          (genericAffineSquare K (Fin (5 * r)) (Fin (4 * r)))
          (genericAffineRows K (Fin (5 * r)) (Fin (4 * r)))) 5) := by
    rw [generic_uniform_four_slHilbert_five r hr, hGL 5]
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
  · rw [generic_uniform_slHilbert_high 4 r (by decide) (by omega)
      (by simp) (by simp) i₀ d (by omega), hGL d]
    simp only [List.map_replicate, List.sum_replicate, smul_eq_mul]
    have h6 : d + 1 - 6 = d - 6 + 1 := by omega
    have h7 : d + 1 - 7 = d - 6 := by omega
    have hD : d + 2 = d - 6 + 8 := by omega
    have hr2 : 4 ≤ r ^ 2 := by nlinarith
    have hsub : 3 * r ^ 2 - 7 + 7 = 3 * r ^ 2 := Nat.sub_add_cancel (by omega)
    rw [h6, h7, hD]
    conv_lhs => rw [← hsub]
    ring

theorem generic_uniform_four_slHilbert {K : Type*} [Field K]
    (r : ℕ) (hr : 2 ≤ r) (d : ℕ) :
    slHilbert (genericAffineSquare K (Fin (5 * r)) (Fin (4 * r)))
      (genericAffineRows K (Fin (5 * r)) (Fin (4 * r))) d =
      8 * (d - 5) + (3 * r ^ 2 - 7) * (d - 6) := by
  let i₀ : Fin (5 * r) := ⟨0, by omega⟩
  rw [slHilbert_eq_matrix_kernel _ _ i₀,
    (hasMinimalKernelDegrees_iff_hilbert _ _).mp
      (generic_uniform_four_sl_minimal_degrees (K := K) r hr i₀) d]
  simp only [List.map_append, List.map_replicate, List.sum_append,
    List.sum_replicate, smul_eq_mul]
  congr 2

end FD56
