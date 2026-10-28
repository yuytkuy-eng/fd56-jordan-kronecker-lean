/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.ThreeOutputTwoAllDepthFrame

/-! Evaluation-independent bounded scalar lifts for the generic three-output residue-two SL pencil. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxHeartbeats 1000000
variable {K : Type*} [Field K] [CharZero K]

theorem generic_three_two_scalar_lifts_zero_injective (q : ℕ) :
    Function.Injective ((threeTwoScalarLiftMatrix q
      (genericAffineSquare K (Fin (3*q+2)) (Fin 3))
      (genericAffineRows K (Fin (3*q+2)) (Fin 3))).map (Polynomial.evalRingHom 0)).mulVec := by
  let φ := (Polynomial.evalRingHom
    (0 : AffineCoefficientField K (MatrixParameters (Fin (3*q+2)) (Fin 3)))).comp
    (affineParameterMap K (MatrixParameters (Fin (3*q+2)) (Fin 3)))
  have hφ : Function.Injective φ := by
    dsimp only [φ]
    rw [affineParameterMap_zero]
    exact (IsFractionRing.injective
      (MvPolynomial (MatrixParameters (Fin (3*q+2)) (Fin 3) ⊕ MatrixParameters (Fin (3*q+2)) (Fin 3)) K)
      (AffineCoefficientField K (MatrixParameters (Fin (3*q+2)) (Fin 3)))).comp
      (MvPolynomial.rename_injective (R:=K)
        (Sum.inl : MatrixParameters (Fin (3*q+2)) (Fin 3) →
          MatrixParameters (Fin (3*q+2)) (Fin 3) ⊕ MatrixParameters (Fin (3*q+2)) (Fin 3))
        Sum.inl_injective)
  let ψ := matrixSpecialization (threeTwoShiftM (R:=K) q) (threeTwoShiftP q)
  let A := threeTwoScalarLiftMatrix q (universalSquare K (Fin (3*q+2)) (Fin 3))
    (universalRows K (Fin (3*q+2)) (Fin 3))
  have hA : Function.Injective (A.map ψ).mulVec := by
    dsimp only [A,ψ]
    rw [threeTwoScalarLiftMatrix_map,
      (universal_pair_specialization (threeTwoShiftM (R:=K) q) (threeTwoShiftP q)).1,
      (universal_pair_specialization (threeTwoShiftM (R:=K) q) (threeTwoShiftP q)).2]
    exact threeTwo_shift_scalar_lift_injective q
  have hg := matrix_injective_of_field_specialization ψ φ hφ A hA
  have he : A.map φ=(threeTwoScalarLiftMatrix q
      (genericAffineSquare K (Fin (3*q+2)) (Fin 3))
      (genericAffineRows K (Fin (3*q+2)) (Fin 3))).map (Polynomial.evalRingHom 0) := by
    dsimp only [A,φ,genericAffineSquare,genericAffineRows]
    rw [← threeTwoScalarLiftMatrix_map,Matrix.map_map]
    rfl
  rw [he] at hg
  exact hg

theorem generic_three_two_sl_kernel_frame (q : ℕ) (i₀ : Fin (3*q+2)) :
    ∃ Z : Matrix (SLInput (Fin (3*q+2)) (Fin 3)) (Fin 3)
      ((AffineCoefficientField K (MatrixParameters (Fin (3*q+2)) (Fin 3)))[X]),
      ((slEquationMatrix (genericAffineSquare K (Fin (3*q+2)) (Fin 3))
        (genericAffineRows K (Fin (3*q+2)) (Fin 3)) i₀) * Z :
          Matrix (SLOutput (Fin (3*q+2)) (Fin 3)) (Fin 3)
            ((AffineCoefficientField K (MatrixParameters (Fin (3*q+2)) (Fin 3)))[X]))=0 ∧
      DegreeBound Z (threeTwoFrameDegree q) ∧
      Function.Injective (Z.map (Polynomial.evalRingHom 0)).mulVec := by
  exact ⟨threeTwoScalarLiftMatrix q _ _,threeTwoScalarLiftMatrix_kernel q _ _ i₀,
    threeTwo_scalar_lift_degree q _ _ (genericAffineSquare_degree K _ _)
      (genericAffineRows_degree K _ _),generic_three_two_scalar_lifts_zero_injective q⟩

end FD56
