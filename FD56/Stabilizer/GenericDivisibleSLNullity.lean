/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.RegularSLRadical
import FD56.Stabilizer.GenericDivisibleGLDeterminant
import FD56.Stabilizer.GenericSquareSLDecomposition

/-! Generic divisible SL pencils have exactly one rational kernel generator. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K : Type*} {m : Type} [Field K] [Fintype m] [DecidableEq m]

theorem generic_divisible_sl_nullity (q : ℕ) (i₀ : Fin (q+1) × m) :
    Module.finrank (GenericPencilField K (Fin (q+1) × m) m)
      (LinearMap.ker (Matrix.toLin' ((slEquationMatrix
        (genericAffineSquare K (Fin (q+1) × m) m)
        (genericAffineRows K (Fin (q+1) × m) m) i₀).map
          (algebraMap _ (GenericPencilField K (Fin (q+1) × m) m)))))=1 := by
  let F := GenericPencilField K (Fin (q+1) × m) m
  let φ := algebraMap (AffineCoefficientField K (MatrixParameters (Fin (q+1) × m) m))[X] F
  let M := genericAffineSquare K (Fin (q+1) × m) m
  let P := genericAffineRows K (Fin (q+1) × m) m
  have hd : (glKirillovMatrix (M.map φ) (P.map φ)).det≠0 := by
    intro hz
    have he := φ.map_det (glKirillovMatrix M P)
    change φ (glKirillovMatrix M P).det=((glKirillovMatrix M P).map φ).det at he
    rw [glKirillovMatrix_map,hz] at he
    exact generic_divisible_gl_kirillov_det_ne_zero K m (q+1)
      ((IsFractionRing.injective _ _) (he.trans (map_zero φ).symm))
  rw [slEquationMatrix_map]
  exact slEquationMatrix_nullity_of_gl_det_ne_zero (M.map φ) (P.map φ) i₀ hd

theorem generic_divisible_sl_kirillov_nullity (q : ℕ) (i₀ : Fin (q+1) × m) :
    Module.finrank (GenericPencilField K (Fin (q+1) × m) m)
      (LinearMap.ker (Matrix.toLin' ((slKirillovMatrix
        (genericAffineSquare K (Fin (q+1) × m) m)
        (genericAffineRows K (Fin (q+1) × m) m) i₀).map
          (algebraMap _ (GenericPencilField K (Fin (q+1) × m) m)))))=1 := by
  rw [slKirillovMatrix_map,slKirillovMatrix_field_finrank]
  have h := generic_divisible_sl_nullity (K:=K) q i₀
  rwa [slEquationMatrix_map,slEquationMatrix_field_finrank] at h

end FD56
