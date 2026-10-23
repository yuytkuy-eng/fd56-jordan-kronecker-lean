/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MixedSLClosure
import FD56.Hilbert.MixedSLCritical

/-! Generic SL minimal degrees for mixed auxiliary degrees at least four. -/

noncomputable section
namespace FD56
open Matrix Polynomial

theorem generic_mixed_sl_minimal_degrees {K : Type*} [Field K]
    (a u v : ℕ) (ha : 4 ≤ a) (hu : 0 < u) (hv : 0 < v)
    (i₀ : Fin ((a + 1) * (u + v) + v)) :
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
  apply generic_mixed_sl_minimal_degrees_of_critical a u v ha hu hv i₀
  have h := generic_mixed_slHilbert_critical (K := K) a u v ha hu hv
    (by simp : Fintype.card (Fin (a * (u + v) + v)) = a * (u + v) + v)
    (by simp only [Fintype.card_fin]; ring :
      Fintype.card (Fin ((a + 1) * (u + v) + v)) =
        Fintype.card (Fin (a * (u + v) + v)) + (u + v)) i₀
  have hsub : a * (u + v) + v - 4 * (u + v) = (a - 4) * (u + v) + v := by
    have hs := Nat.sub_add_cancel ha
    have he : a * (u + v) + v = (a - 4) * (u + v) + v + 4 * (u + v) := by
      nlinarith only [congrArg (fun z => z * (u + v)) hs]
    omega
  simpa only [Fintype.card_fin, hsub, Nat.mul_right_comm 3 (u + v) v] using h

end FD56
