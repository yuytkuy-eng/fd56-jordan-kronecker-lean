/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.ThreeOutputTwoScalarLifts

/-! Evaluation-independent bounded scalar lifts for the generic fourteen-state SL pencil. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K : Type*} [Field K] [CharZero K]

theorem generic_fourteen_three_scalar_lifts_zero_injective :
    Function.Injective ((threeTwoScalarLiftMatrix 4
      (genericAffineSquare K (Fin 14) (Fin 3))
      (genericAffineRows K (Fin 14) (Fin 3))).map (Polynomial.evalRingHom 0)).mulVec := by
  let φ := (Polynomial.evalRingHom
    (0 : AffineCoefficientField K (MatrixParameters (Fin 14) (Fin 3)))).comp
    (affineParameterMap K (MatrixParameters (Fin 14) (Fin 3)))
  have hφ : Function.Injective φ := by
    dsimp only [φ]
    rw [affineParameterMap_zero]
    exact (IsFractionRing.injective
      (MvPolynomial (MatrixParameters (Fin 14) (Fin 3) ⊕ MatrixParameters (Fin 14) (Fin 3)) K)
      (AffineCoefficientField K (MatrixParameters (Fin 14) (Fin 3)))).comp
      (MvPolynomial.rename_injective (R:=K)
        (Sum.inl : MatrixParameters (Fin 14) (Fin 3) →
          MatrixParameters (Fin 14) (Fin 3) ⊕ MatrixParameters (Fin 14) (Fin 3))
        Sum.inl_injective)
  let ψ := matrixSpecialization (threeTwoShiftM (R:=K) 4) (threeTwoShiftP 4)
  let A := threeTwoScalarLiftMatrix 4 (universalSquare K (Fin 14) (Fin 3))
    (universalRows K (Fin 14) (Fin 3))
  have hA : Function.Injective (A.map ψ).mulVec := by
    dsimp only [A,ψ]
    rw [threeTwoScalarLiftMatrix_map,
      (universal_pair_specialization (threeTwoShiftM (R:=K) 4) (threeTwoShiftP 4)).1,
      (universal_pair_specialization (threeTwoShiftM (R:=K) 4) (threeTwoShiftP 4)).2]
    exact fourteenThree_shift_scalar_lift_injective
  have hg := matrix_injective_of_field_specialization ψ φ hφ A hA
  have he : A.map φ=(threeTwoScalarLiftMatrix 4
      (genericAffineSquare K (Fin 14) (Fin 3))
      (genericAffineRows K (Fin 14) (Fin 3))).map (Polynomial.evalRingHom 0) := by
    dsimp only [A,φ,genericAffineSquare,genericAffineRows]
    rw [← threeTwoScalarLiftMatrix_map,Matrix.map_map]
    rfl
  rw [he] at hg
  exact hg

theorem generic_fourteen_three_scalar_lifts_degree :
    DegreeBound (threeTwoScalarLiftMatrix 4
      (genericAffineSquare K (Fin 14) (Fin 3))
      (genericAffineRows K (Fin 14) (Fin 3))) 39 :=
  fourteenThree_scalar_lift_degree _ _
    (genericAffineSquare_degree K _ _) (genericAffineRows_degree K _ _)

theorem generic_fourteen_three_scalar_lifts_kernel (i₀ : Fin 14) :
    slEquationMatrix (genericAffineSquare K (Fin 14) (Fin 3))
      (genericAffineRows K (Fin 14) (Fin 3)) i₀ *
      threeTwoScalarLiftMatrix 4 (genericAffineSquare K (Fin 14) (Fin 3))
        (genericAffineRows K (Fin 14) (Fin 3))=0 :=
  threeTwoScalarLiftMatrix_kernel 4 _ _ i₀

theorem generic_fourteen_three_sl_kernel_frame (i₀ : Fin 14) :
    ∃ Z : Matrix (SLInput (Fin 14) (Fin 3)) (Fin 3)
      (AffineCoefficientField K (MatrixParameters (Fin 14) (Fin 3)))[X],
      slEquationMatrix (genericAffineSquare K (Fin 14) (Fin 3))
        (genericAffineRows K (Fin 14) (Fin 3)) i₀*Z=0 ∧ DegreeBound Z 39 ∧
      Function.Injective (Z.map (Polynomial.evalRingHom 0)).mulVec := by
  exact ⟨threeTwoScalarLiftMatrix 4 _ _,generic_fourteen_three_scalar_lifts_kernel i₀,
    generic_fourteen_three_scalar_lifts_degree,generic_fourteen_three_scalar_lifts_zero_injective⟩

end FD56
