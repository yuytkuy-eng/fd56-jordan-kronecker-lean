/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GenericDivisibleSLRoot
import FD56.Stabilizer.RegularSLRadical

/-! The complete finite nullity profile of a generic divisible SL pencil. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K L : Type*} {m : Type} [Field K] [Field L] [Fintype m] [DecidableEq m]
local instance genericDivisibleSLRankLocusDecidableEq : DecidableEq L := Classical.decEq L

theorem generic_divisible_sl_nonpole_nullity (q : ℕ) (hm : 2≤Fintype.card m)
    (φ : AffineCoefficientField K (MatrixParameters (Fin (q+1) × m) m) →+* L)
    (x : L) (i₀ : Fin (q+1) × m)
    (hx : (glKirillovMatrix (genericAffineSquare K (Fin (q+1) × m) m)
      (genericAffineRows K (Fin (q+1) × m) m)).det.eval₂ φ x≠0) :
    Module.finrank L (LinearMap.ker (Matrix.toLin'
      ((slKirillovMatrix (genericAffineSquare K (Fin (q+1) × m) m)
        (genericAffineRows K (Fin (q+1) × m) m) i₀).map (Polynomial.eval₂RingHom φ x))))=1 := by
  letI : Nonempty (Fin (q+1) × m) := ⟨i₀⟩
  let ev := Polynomial.eval₂RingHom φ x
  let M := (genericAffineSquare K (Fin (q+1) × m) m).map ev
  let P := (genericAffineRows K (Fin (q+1) × m) m).map ev
  have hd : (glKirillovMatrix M P).det≠0 := by
    rw [show glKirillovMatrix M P=(glKirillovMatrix
      (genericAffineSquare K (Fin (q+1) × m) m)
      (genericAffineRows K (Fin (q+1) × m) m)).map ev from (glKirillovMatrix_map ev _ _).symm]
    intro hz
    exact hx ((ev.map_det _).trans hz)
  rw [slKirillovMatrix_map]
  exact slKirillovMatrix_nullity_of_gl_det_ne_zero M P i₀ hd

theorem generic_divisible_sl_finite_nullity (q : ℕ) (hm : 2≤Fintype.card m)
    (φ : AffineCoefficientField K (MatrixParameters (Fin (q+1) × m) m) →+* L)
    (x : L) (i₀ : Fin (q+1) × m) :
    let H := glKirillovMatrix (genericAffineSquare K (Fin (q+1) × m) m)
      (genericAffineRows K (Fin (q+1) × m) m)
    Module.finrank L (LinearMap.ker (Matrix.toLin'
      ((slKirillovMatrix (genericAffineSquare K (Fin (q+1) × m) m)
        (genericAffineRows K (Fin (q+1) × m) m) i₀).map (Polynomial.eval₂RingHom φ x))))=
      if H.det.eval₂ φ x=0 then 2*Fintype.card m-1 else 1 := by
  classical
  dsimp only
  split_ifs with hx
  · exact generic_divisible_sl_pole_nullity q hm φ x i₀ hx
  · exact generic_divisible_sl_nonpole_nullity q hm φ x i₀ hx

end FD56
