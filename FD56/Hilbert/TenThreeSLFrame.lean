/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.ThreeOutputOneScalarLifts

/-! A verified rank-three frame of degree at most twenty-one in the generic SL kernel. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K : Type*} [Field K] [CharZero K]

theorem generic_ten_three_scalar_lift_at_zero_injective :
    Function.Injective ((threeOneScalarLiftMatrix 3
      (genericAffineSquare K (Fin 10) (Fin 3))
      (genericAffineRows K (Fin 10) (Fin 3))).map (Polynomial.evalRingHom 0)).mulVec := by
  let σ := MatrixParameters (Fin 10) (Fin 3)
  let φ := (Polynomial.evalRingHom (0 : AffineCoefficientField K σ)).comp (affineParameterMap K σ)
  have hφ : Function.Injective φ := by
    dsimp only [φ]
    rw [affineParameterMap_zero]
    exact (IsFractionRing.injective _ _).comp
      (MvPolynomial.rename_injective (R:=K) (Sum.inl : σ → σ ⊕ σ) Sum.inl_injective)
  let M := threeOneShiftM (R:=K) 3
  let P := threeOneShiftP (R:=K) 3
  let A := threeOneScalarLiftMatrix 3 (universalSquare K (Fin 10) (Fin 3))
    (universalRows K (Fin 10) (Fin 3))
  have hs : A.map (matrixSpecialization M P)=threeOneScalarLiftMatrix 3 M P := by
    dsimp only [A]
    rw [threeOneScalarLiftMatrix_map,(universal_pair_specialization M P).1,
      (universal_pair_specialization M P).2]
  have hi : Function.Injective (A.map φ).mulVec :=
    matrix_injective_of_field_specialization (matrixSpecialization M P) φ hφ A
      (hs ▸ tenThree_shift_scalar_lift_injective (K:=K))
  have hg : A.map φ=(threeOneScalarLiftMatrix 3
      (genericAffineSquare K (Fin 10) (Fin 3))
      (genericAffineRows K (Fin 10) (Fin 3))).map (Polynomial.evalRingHom 0) := by
    dsimp only [A,φ,genericAffineSquare,genericAffineRows]
    rw [← threeOneScalarLiftMatrix_map]
    rfl
  exact hg ▸ hi

theorem generic_ten_three_sl_kernel_frame (i₀ : Fin 10) :
    ∃ Z : Matrix (SLInput (Fin 10) (Fin 3)) (Fin 3)
      (AffineCoefficientField K (MatrixParameters (Fin 10) (Fin 3)))[X],
      slEquationMatrix (genericAffineSquare K (Fin 10) (Fin 3))
        (genericAffineRows K (Fin 10) (Fin 3)) i₀*Z=0 ∧ DegreeBound Z 21 ∧
      Function.Injective (Z.map (Polynomial.evalRingHom 0)).mulVec := by
  exact ⟨threeOneScalarLiftMatrix 3 _ _,threeOneScalarLiftMatrix_kernel 3 _ _ i₀,
    tenThree_scalar_lift_degree _ _ (genericAffineSquare_degree K _ _)
      (genericAffineRows_degree K _ _),generic_ten_three_scalar_lift_at_zero_injective⟩

end FD56
