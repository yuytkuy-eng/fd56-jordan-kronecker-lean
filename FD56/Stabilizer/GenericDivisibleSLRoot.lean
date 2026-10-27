/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.FieldSLKirillovKernel
import FD56.Stabilizer.ObservableRadical
import FD56.Stabilizer.GenericDivisibleGLRoot
import FD56.Stabilizer.GenericSquareSLDecomposition

/-! The actual generic divisible SL pencil has nullity 2m-1 at each finite pole. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K L : Type*} {m : Type} [Field K] [Field L] [Fintype m] [DecidableEq m]

theorem generic_divisible_sl_observability_root_nullity (q : ℕ)
    (hm : 2≤Fintype.card m)
    (φ : AffineCoefficientField K (MatrixParameters (Fin (q+1) × m) m) →+* L)
    (x : L) (i₀ : Fin (q+1) × m)
    (hx : (observabilityMatrix (genericAffineSquare K (Fin (q+1) × m) m)
      (genericAffineRows K (Fin (q+1) × m) m) (q+1)).det.eval₂ φ x=0) :
    Module.finrank L (LinearMap.ker (Matrix.toLin'
      ((slKirillovMatrix (genericAffineSquare K (Fin (q+1) × m) m)
        (genericAffineRows K (Fin (q+1) × m) m) i₀).map (Polynomial.eval₂RingHom φ x))))=
      2*Fintype.card m-1 := by
  letI : Nonempty (Fin (q+1) × m) := ⟨i₀⟩
  obtain ⟨hbefore,hfirst,hnext⟩ := generic_divisible_observability_root_profile q hm φ x hx
  rw [slKirillovMatrix_map,slKirillovMatrix_field_finrank,
    observable_sl_radical_finrank _ _ (q+2) hnext,
    gl_finrank_of_simple_observability_defect q _ _ hm (by simp) hbefore hfirst hnext]
  omega

theorem generic_divisible_sl_pole_nullity (q : ℕ) (hm : 2≤Fintype.card m)
    (φ : AffineCoefficientField K (MatrixParameters (Fin (q+1) × m) m) →+* L)
    (x : L) (i₀ : Fin (q+1) × m)
    (hx : (glKirillovMatrix (genericAffineSquare K (Fin (q+1) × m) m)
      (genericAffineRows K (Fin (q+1) × m) m)).det.eval₂ φ x=0) :
    Module.finrank L (LinearMap.ker (Matrix.toLin'
      ((slKirillovMatrix (genericAffineSquare K (Fin (q+1) × m) m)
        (genericAffineRows K (Fin (q+1) × m) m) i₀).map (Polynomial.eval₂RingHom φ x))))=
      2*Fintype.card m-1 := by
  apply generic_divisible_sl_observability_root_nullity q hm φ x i₀
  rw [generic_divisible_gl_kirillov_determinant,Polynomial.eval₂_pow] at hx
  exact pow_eq_zero hx

end FD56
