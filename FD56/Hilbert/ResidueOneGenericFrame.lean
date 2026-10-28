/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.ResidueOneAllDepthFrame

/-! Evaluation-independent bounded scalar lifts for the generic residue-one SL pencil. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxHeartbeats 1000000
variable (m : ℕ) [NeZero m]
variable {K : Type*} [Field K] [CharZero K]

theorem generic_residue_one_scalar_lifts_zero_injective (q : ℕ) :
    Function.Injective ((residueOneScalarLiftMatrix m q
      (genericAffineSquare K (Fin (m*q+1)) (Fin m))
      (genericAffineRows K (Fin (m*q+1)) (Fin m))).map (Polynomial.evalRingHom 0)).mulVec := by
  let φ := (Polynomial.evalRingHom
    (0 : AffineCoefficientField K (MatrixParameters (Fin (m*q+1)) (Fin m)))).comp
    (affineParameterMap K (MatrixParameters (Fin (m*q+1)) (Fin m)))
  have hφ : Function.Injective φ := by
    dsimp only [φ]
    rw [affineParameterMap_zero]
    exact (IsFractionRing.injective
      (MvPolynomial (MatrixParameters (Fin (m*q+1)) (Fin m) ⊕ MatrixParameters (Fin (m*q+1)) (Fin m)) K)
      (AffineCoefficientField K (MatrixParameters (Fin (m*q+1)) (Fin m)))).comp
      (MvPolynomial.rename_injective (R:=K)
        (Sum.inl : MatrixParameters (Fin (m*q+1)) (Fin m) →
          MatrixParameters (Fin (m*q+1)) (Fin m) ⊕ MatrixParameters (Fin (m*q+1)) (Fin m))
        Sum.inl_injective)
  let ψ := matrixSpecialization (residueOneShiftM (R:=K) m q) (residueOneShiftP m q)
  let A := residueOneScalarLiftMatrix m q (universalSquare K (Fin (m*q+1)) (Fin m))
    (universalRows K (Fin (m*q+1)) (Fin m))
  have hA : Function.Injective (A.map ψ).mulVec := by
    dsimp only [A,ψ]
    rw [residueOneScalarLiftMatrix_map,
      (universal_pair_specialization (residueOneShiftM (R:=K) m q) (residueOneShiftP m q)).1,
      (universal_pair_specialization (residueOneShiftM (R:=K) m q) (residueOneShiftP m q)).2]
    exact residueOne_shift_scalar_lift_injective m q
  have hg := matrix_injective_of_field_specialization ψ φ hφ A hA
  have he : A.map φ=(residueOneScalarLiftMatrix m q
      (genericAffineSquare K (Fin (m*q+1)) (Fin m))
      (genericAffineRows K (Fin (m*q+1)) (Fin m))).map (Polynomial.evalRingHom 0) := by
    dsimp only [A,φ,genericAffineSquare,genericAffineRows]
    rw [← residueOneScalarLiftMatrix_map,Matrix.map_map]
    rfl
  rw [he] at hg
  exact hg

theorem generic_residue_one_sl_kernel_frame (q : ℕ) (i₀ : Fin (m*q+1)) :
    ∃ Z : Matrix (SLInput (Fin (m*q+1)) (Fin m)) (Fin m)
      ((AffineCoefficientField K (MatrixParameters (Fin (m*q+1)) (Fin m)))[X]),
      ((slEquationMatrix (genericAffineSquare K (Fin (m*q+1)) (Fin m))
        (genericAffineRows K (Fin (m*q+1)) (Fin m)) i₀) * Z :
          Matrix (SLOutput (Fin (m*q+1)) (Fin m)) (Fin m)
            ((AffineCoefficientField K (MatrixParameters (Fin (m*q+1)) (Fin m)))[X]))=0 ∧
      DegreeBound Z (residueOneFrameDegree m q) ∧
      Function.Injective (Z.map (Polynomial.evalRingHom 0)).mulVec := by
  exact ⟨residueOneScalarLiftMatrix m q _ _,residueOneScalarLiftMatrix_kernel m q _ _ i₀,
    residueOne_scalar_lift_degree m q _ _ (genericAffineSquare_degree K _ _)
      (genericAffineRows_degree K _ _),generic_residue_one_scalar_lifts_zero_injective m q⟩

end FD56
