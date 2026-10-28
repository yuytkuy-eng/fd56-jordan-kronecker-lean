/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.TerminalCorankOneAllDepthFrame

/-! Bounded independent scalar lifts for every generic terminal-corank-one SL pencil. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxHeartbeats 1000000
variable (s : ℕ)
variable {K : Type*} [Field K] [CharZero K]

theorem generic_terminal_one_scalar_lifts_zero_injective (q : ℕ) :
    Function.Injective ((terminalOneScalarLiftMatrix s q
      (genericAffineSquare K (Fin ((s+2)*q+s+1)) (Fin (s+2)))
      (genericAffineRows K (Fin ((s+2)*q+s+1)) (Fin (s+2)))).map (Polynomial.evalRingHom 0)).mulVec := by
  let φ := (Polynomial.evalRingHom
    (0 : AffineCoefficientField K (MatrixParameters (Fin ((s+2)*q+s+1)) (Fin (s+2))))).comp
    (affineParameterMap K (MatrixParameters (Fin ((s+2)*q+s+1)) (Fin (s+2))))
  have hφ : Function.Injective φ := by
    dsimp only [φ]
    rw [affineParameterMap_zero]
    exact (IsFractionRing.injective
      (MvPolynomial (MatrixParameters (Fin ((s+2)*q+s+1)) (Fin (s+2)) ⊕ MatrixParameters (Fin ((s+2)*q+s+1)) (Fin (s+2))) K)
      (AffineCoefficientField K (MatrixParameters (Fin ((s+2)*q+s+1)) (Fin (s+2))))).comp
      (MvPolynomial.rename_injective (R:=K)
        (Sum.inl : MatrixParameters (Fin ((s+2)*q+s+1)) (Fin (s+2)) →
          MatrixParameters (Fin ((s+2)*q+s+1)) (Fin (s+2)) ⊕ MatrixParameters (Fin ((s+2)*q+s+1)) (Fin (s+2)))
        Sum.inl_injective)
  let ψ := matrixSpecialization (terminalOneShiftM (R:=K) s q) (terminalOneShiftP s q)
  let A := terminalOneScalarLiftMatrix s q (universalSquare K (Fin ((s+2)*q+s+1)) (Fin (s+2)))
    (universalRows K (Fin ((s+2)*q+s+1)) (Fin (s+2)))
  have hA : Function.Injective (A.map ψ).mulVec := by
    dsimp only [A,ψ]
    rw [terminalOneScalarLiftMatrix_map,
      (universal_pair_specialization (terminalOneShiftM (R:=K) s q) (terminalOneShiftP s q)).1,
      (universal_pair_specialization (terminalOneShiftM (R:=K) s q) (terminalOneShiftP s q)).2]
    exact terminalOne_shift_scalar_lift_injective s q
  have hg := matrix_injective_of_field_specialization ψ φ hφ A hA
  have he : A.map φ=(terminalOneScalarLiftMatrix s q
      (genericAffineSquare K (Fin ((s+2)*q+s+1)) (Fin (s+2)))
      (genericAffineRows K (Fin ((s+2)*q+s+1)) (Fin (s+2)))).map (Polynomial.evalRingHom 0) := by
    dsimp only [A,φ,genericAffineSquare,genericAffineRows]
    rw [← terminalOneScalarLiftMatrix_map,Matrix.map_map]
    rfl
  rw [he] at hg
  exact hg

theorem generic_terminal_one_sl_kernel_frame (q : ℕ) (i₀ : Fin ((s+2)*q+s+1)) :
    ∃ Z : Matrix (SLInput (Fin ((s+2)*q+s+1)) (Fin (s+2))) (Fin (s+2))
      ((AffineCoefficientField K (MatrixParameters (Fin ((s+2)*q+s+1)) (Fin (s+2))))[X]),
      ((slEquationMatrix (genericAffineSquare K (Fin ((s+2)*q+s+1)) (Fin (s+2)))
        (genericAffineRows K (Fin ((s+2)*q+s+1)) (Fin (s+2))) i₀) * Z :
          Matrix (SLOutput (Fin ((s+2)*q+s+1)) (Fin (s+2))) (Fin (s+2))
            ((AffineCoefficientField K (MatrixParameters (Fin ((s+2)*q+s+1)) (Fin (s+2))))[X]))=0 ∧
      DegreeBound Z (terminalOneFrameDegree s q) ∧
      Function.Injective (Z.map (Polynomial.evalRingHom 0)).mulVec := by
  exact ⟨terminalOneScalarLiftMatrix s q _ _,terminalOneScalarLiftMatrix_kernel s q _ _ i₀,
    terminalOne_scalar_lift_degree s q _ _ (genericAffineSquare_degree K _ _)
      (genericAffineRows_degree K _ _),generic_terminal_one_scalar_lifts_zero_injective s q⟩

end FD56
