/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.KirillovCoefficient
import FD56.Stabilizer.RegularSLRadical
import FD56.Stabilizer.GenericDivisibleGLDeterminant

/-! The generic divisible SL pencil has no nullity jump at infinity. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K : Type*} {m : Type} [Field K] [Fintype m] [DecidableEq m]

theorem generic_divisible_sl_leading_nullity (q : ℕ) (i₀ : Fin (q+1) × m) :
    Module.finrank (AffineCoefficientField K (MatrixParameters (Fin (q+1) × m) m))
      (LinearMap.ker (Matrix.toLin' (fun i j =>
        (slKirillovMatrix (genericAffineSquare K (Fin (q+1) × m) m)
          (genericAffineRows K (Fin (q+1) × m) m) i₀ i j).coeff 1)))=1 := by
  rw [slKirillovMatrix_coefficient]
  apply slKirillovMatrix_nullity_of_gl_det_ne_zero
  rw [← glKirillovMatrix_coefficient]
  exact generic_divisible_gl_leading_det_ne_zero K m (q+1)

end FD56
