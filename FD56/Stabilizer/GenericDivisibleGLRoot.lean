/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GenericDivisibleRootProfile
import FD56.Stabilizer.GLSimplePoleKernel
import FD56.Stabilizer.GenericDivisibleGLDeterminant
import FD56.Stabilizer.GenericSquareGLJordan

/-! Exact nullity and determinant order at every finite pole of a divisible generic GL pencil.
These local invariants alone are not a constant canonical decomposition. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K L : Type*} {m : Type} [Field K] [Field L] [Fintype m] [DecidableEq m]

theorem generic_divisible_gl_observability_root_nullity (q : ℕ)
    (hm : 2≤Fintype.card m)
    (φ : AffineCoefficientField K (MatrixParameters (Fin (q+1) × m) m) →+* L) (x : L)
    (hx : (observabilityMatrix (genericAffineSquare K (Fin (q+1) × m) m)
      (genericAffineRows K (Fin (q+1) × m) m) (q+1)).det.eval₂ φ x=0) :
    Module.finrank L (LinearMap.ker (Matrix.toLin'
      ((glKirillovMatrix (genericAffineSquare K (Fin (q+1) × m) m)
        (genericAffineRows K (Fin (q+1) × m) m)).map (Polynomial.eval₂RingHom φ x)))) =
      2*Fintype.card m-2 := by
  obtain ⟨hbefore,hfirst,hnext⟩ := generic_divisible_observability_root_profile q hm φ x hx
  rw [glKirillovMatrix_map]
  exact glKirillovMatrix_simple_observability_defect_nullity q _ _ hm
    (by simp) hbefore hfirst hnext

theorem generic_divisible_gl_pole_nullity_and_order (q : ℕ)
    (hm : 2≤Fintype.card m)
    (φ : AffineCoefficientField K (MatrixParameters (Fin (q+1) × m) m) →+* L) (x : L)
    (hx : (glKirillovMatrix (genericAffineSquare K (Fin (q+1) × m) m)
      (genericAffineRows K (Fin (q+1) × m) m)).det.eval₂ φ x=0) :
    let H := glKirillovMatrix (genericAffineSquare K (Fin (q+1) × m) m)
      (genericAffineRows K (Fin (q+1) × m) m)
    Module.finrank L (LinearMap.ker (Matrix.toLin' (H.map (Polynomial.eval₂RingHom φ x)))) =
      2*Fintype.card m-2 ∧ rootMultiplicity x (H.det.map φ)=2*Fintype.card m := by
  have hO : (observabilityMatrix (genericAffineSquare K (Fin (q+1) × m) m)
      (genericAffineRows K (Fin (q+1) × m) m) (q+1)).det.eval₂ φ x=0 := by
    rw [generic_divisible_gl_kirillov_determinant,Polynomial.eval₂_pow] at hx
    exact pow_eq_zero hx
  refine ⟨generic_divisible_gl_observability_root_nullity q hm φ x hO, ?_⟩
  apply generic_divisible_gl_det_rootMultiplicity K m (q+1) φ x
  simpa only [Polynomial.IsRoot.def,Polynomial.eval_map] using hO

end FD56
