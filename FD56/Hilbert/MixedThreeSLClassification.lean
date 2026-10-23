/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MixedThreeSLClosure
import FD56.Hilbert.MixedThreeSLRealization

/-! Generic SL minimal degrees for mixed auxiliary degrees three and four. -/

noncomputable section
namespace FD56
open Matrix Polynomial

theorem generic_mixed_three_sl_minimal_degrees {K : Type*} [Field K]
    (u v : ℕ) (hu : 0 < u) (hv : 0 < v)
    (i₀ : Fin (4*(u+v)+v)) :
    let A := u*(u+3*v)
    let B := u^2+u*v+3*v^2
    let C := u*v
    let t := 8-C
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (4*(u+v)+v)) (Fin (3*(u+v)+v)))
      (genericAffineRows K (Fin (4*(u+v)+v)) (Fin (3*(u+v)+v))) i₀)
      (List.replicate (A+t) 6 ++ List.replicate (B+9-2*t) 7 ++
        List.replicate (C-8) 8) := by
  apply generic_mixed_three_sl_minimal_degrees_of_critical u v hu hv i₀
  · exact generic_mixed_three_slHilbert_five u v hu hv (by simp)
      (by simp only [Fintype.card_fin]; ring) i₀
  · exact generic_mixed_three_slHilbert_six u v hu hv (by simp)
      (by simp only [Fintype.card_fin]; ring) i₀

end FD56
