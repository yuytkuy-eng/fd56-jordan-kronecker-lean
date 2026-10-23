/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MixedTwoSLClosure
import FD56.Hilbert.MixedTwoSLFive

/-! Generic SL minimal degrees for mixed auxiliary degrees two and three. -/

noncomputable section
namespace FD56
open Matrix Polynomial

theorem generic_mixed_two_sl_minimal_degrees_le {K : Type*} [Field K]
    (u v : ℕ) (hu : 0 < u) (hv : 0 < v) (huv : u ≤ v)
    (i₀ : Fin (3*(u+v)+v)) :
    let A := u*(v-u)
    let B := 2*u^2+v^2
    let C := v*(2*u+v)
    let t := 7-C
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (3*(u+v)+v)) (Fin (2*(u+v)+v)))
      (genericAffineRows K (Fin (3*(u+v)+v)) (Fin (2*(u+v)+v))) i₀)
      (List.replicate (A+t) 5 ++ List.replicate (B+8-2*t) 6 ++
        List.replicate (C-7) 7) := by
  apply generic_mixed_two_sl_minimal_degrees_le_of_five u v hu hv huv i₀
  exact generic_mixed_two_slHilbert_five_le u v hu hv huv (by simp)
    (by simp only [Fintype.card_fin]; ring) i₀

theorem generic_mixed_two_sl_minimal_degrees_gt {K : Type*} [Field K]
    (u v : ℕ) (hu : 0 < u) (hv : 0 < v) (hvu : v < u)
    (i₀ : Fin (3*(u+v)+v)) :
    let A := 3*u*v
    let B := u*(u-v)+3*v^2
    let C := v*(u-v)
    let t := 8-C
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (3*(u+v)+v)) (Fin (2*(u+v)+v)))
      (genericAffineRows K (Fin (3*(u+v)+v)) (Fin (2*(u+v)+v))) i₀)
      (List.replicate (A+t) 6 ++ List.replicate (B+9-2*t) 7 ++
        List.replicate (C-8) 8) := by
  apply generic_mixed_two_sl_minimal_degrees_gt_of_five u v hu hv hvu i₀
  exact generic_mixed_two_slHilbert_five_gt u v hu hv hvu (by simp)
    (by simp only [Fintype.card_fin]; ring) i₀

end FD56
