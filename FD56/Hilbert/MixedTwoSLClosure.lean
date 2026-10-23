/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MixedTwoGL
import FD56.Hilbert.MixedTwoSLRealization
import FD56.Hilbert.ScalarCorrectionCriterion
import FD56.Hilbert.FamilySLClosure

/-! Recovery of mixed two-block SL degree lists from the degree-five value. -/

noncomputable section
namespace FD56
open Matrix Polynomial

theorem generic_mixed_two_sl_minimal_degrees_le_of_five {K : Type*} [Field K]
    (u v : ℕ) (hu : 0 < u) (hv : 0 < v) (huv : u ≤ v)
    (i₀ : Fin (3*(u+v)+v))
    (hfive : slHilbert
      (genericAffineSquare K (Fin (3*(u+v)+v)) (Fin (2*(u+v)+v)))
      (genericAffineRows K (Fin (3*(u+v)+v)) (Fin (2*(u+v)+v))) 5 =
      u*(v-u)+(7-v*(2*u+v))) :
    let A := u*(v-u)
    let B := 2*u^2+v^2
    let C := v*(2*u+v)
    let t := 7-C
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (3*(u+v)+v)) (Fin (2*(u+v)+v)))
      (genericAffineRows K (Fin (3*(u+v)+v)) (Fin (2*(u+v)+v))) i₀)
      (List.replicate (A+t) 5 ++ List.replicate (B+8-2*t) 6 ++
        List.replicate (C-7) 7) := by
  apply hasMinimalKernelDegrees_three_of_scalar_correction _
    (glEquationMatrix
      (genericAffineSquare K (Fin (3*(u+v)+v)) (Fin (2*(u+v)+v)))
      (genericAffineRows K (Fin (3*(u+v)+v)) (Fin (2*(u+v)+v))))
    5 (u*(v-u)) (2*u^2+v^2) (v*(2*u+v))
  · nlinarith
  · exact generic_mixed_two_gl_minimal_degrees_le u v hu hv huv
  · intro d hd
    rw [← slHilbert_eq_matrix_kernel _ _ i₀]
    exact generic_mixed_two_slHilbert_low u v hu hv (by simp)
      (by simp only [Fintype.card_fin]; ring) i₀ d (by omega)
  · rw [← slHilbert_eq_matrix_kernel _ _ i₀]
    exact hfive
  · intro d hd
    rw [← slHilbert_eq_matrix_kernel _ _ i₀]
    exact generic_mixed_two_slHilbert_high_of_le u v hu huv (by simp)
      (by simp only [Fintype.card_fin]; ring) i₀ d (by omega)

theorem generic_mixed_two_sl_minimal_degrees_gt_of_five {K : Type*} [Field K]
    (u v : ℕ) (hu : 0 < u) (hv : 0 < v) (hvu : v < u)
    (i₀ : Fin (3*(u+v)+v))
    (hfive : slHilbert
      (genericAffineSquare K (Fin (3*(u+v)+v)) (Fin (2*(u+v)+v)))
      (genericAffineRows K (Fin (3*(u+v)+v)) (Fin (2*(u+v)+v))) 5 = 0) :
    let A := 3*u*v
    let B := u*(u-v)+3*v^2
    let C := v*(u-v)
    let t := 8-C
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (3*(u+v)+v)) (Fin (2*(u+v)+v)))
      (genericAffineRows K (Fin (3*(u+v)+v)) (Fin (2*(u+v)+v))) i₀)
      (List.replicate (A+t) 6 ++ List.replicate (B+9-2*t) 7 ++
        List.replicate (C-8) 8) := by
  have hGL := generic_mixed_two_gl_minimal_degrees_gt (K := K) u v hu hv hvu
  have h5 : slHilbert
      (genericAffineSquare K (Fin (3*(u+v)+v)) (Fin (2*(u+v)+v)))
      (genericAffineRows K (Fin (3*(u+v)+v)) (Fin (2*(u+v)+v))) 5 =
      Module.finrank (AffineCoefficientField K
        (MatrixParameters (Fin (3*(u+v)+v)) (Fin (2*(u+v)+v))))
        (polynomialKernelAtDegree (glEquationMatrix
          (genericAffineSquare K (Fin (3*(u+v)+v)) (Fin (2*(u+v)+v)))
          (genericAffineRows K (Fin (3*(u+v)+v)) (Fin (2*(u+v)+v)))) 5) := by
    rw [hfive,(hasMinimalKernelDegrees_iff_hilbert _ _).mp hGL 5]
    simp
  apply hasMinimalKernelDegrees_three_of_scalar_correction _
    (glEquationMatrix
      (genericAffineSquare K (Fin (3*(u+v)+v)) (Fin (2*(u+v)+v)))
      (genericAffineRows K (Fin (3*(u+v)+v)) (Fin (2*(u+v)+v))))
    6 (3*u*v) (u*(u-v)+3*v^2) (v*(u-v))
  · have hw : 0 < u-v := Nat.sub_pos_of_lt hvu
    nlinarith
  · exact hGL
  · intro d hd
    rw [← slHilbert_eq_matrix_kernel _ _ i₀,
      generic_middle_slHilbert_eq_gl_below_of_eq_at_degree i₀
        (by simp; omega) (by simp; omega) 5 d (by omega) h5,
      (hasMinimalKernelDegrees_iff_hilbert _ _).mp hGL d]
    have h6 : d+1-6 = 0 := by omega
    have h7 : d+1-7 = 0 := by omega
    have h8 : d+1-8 = 0 := by omega
    simp [h6,h7,h8]
  · rw [← slHilbert_eq_matrix_kernel _ _ i₀]
    exact generic_mixed_two_slHilbert_six_of_ge u v hu hv hvu.le (by simp)
      (by simp only [Fintype.card_fin]; ring) i₀
  · intro d hd
    rw [← slHilbert_eq_matrix_kernel _ _ i₀]
    exact generic_mixed_two_slHilbert_high u v hu (by simp)
      (by simp only [Fintype.card_fin]; ring) i₀ d (by omega)

end FD56
