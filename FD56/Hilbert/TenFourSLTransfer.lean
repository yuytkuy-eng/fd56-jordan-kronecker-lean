/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.FourOutputInteriorSLTests
import FD56.Hilbert.GenericKernelBound

/-! A complete affine witness determines the generic ten-state, four-output SL profile. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K : Type*} [Field K]

theorem generic_ten_four_sl_classification_of_witness
    (M : Matrix (Fin 10) (Fin 10) K[X]) (P : Matrix (Fin 4) (Fin 10) K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hw : HasMinimalKernelDegrees (slEquationMatrix M P (9 : Fin 10)) [13,13,13,14,14])
    (i₀ : Fin 10) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin 10) (Fin 4))
      (genericAffineRows K (Fin 10) (Fin 4)) i₀) [13,13,13,14,14] ∧
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K (Fin 10) (Fin 4))
      (genericAffineRows K (Fin 10) (Fin 4)) i₀) [13,13,13,14,14] := by
  have hwH (d : ℕ) : slHilbert M P d=3*(d+1-13)+2*(d+1-14) := by
    rw [slHilbert_eq_matrix_kernel M P (9 : Fin 10),
      (hasMinimalKernelDegrees_iff_hilbert _ _).mp hw]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    omega
  have h₁ := generic_slHilbert_le_witness M P hM hP (9 : Fin 10) 12
  have h₂ := generic_slHilbert_le_witness M P hM hP (9 : Fin 10) 13
  rw [hwH] at h₁ h₂
  obtain ⟨hmin,_⟩ := generic_four_output_interior_sl_balanced_of_two_tests (K:=K)
    2 (by decide) i₀ (by norm_num at h₁ ⊢; exact h₁) (by norm_num at h₂ ⊢; exact h₂)
  have hfinal : HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin 10) (Fin 4))
      (genericAffineRows K (Fin 10) (Fin 4)) i₀) [13,13,13,14,14] := by
    obtain ⟨r,B,e,hB,hlead,hperm⟩ := hmin
    refine ⟨r,B,e,hB,hlead,hperm.trans ?_⟩
    norm_num [balancedDegreeList]
    decide
  refine ⟨hfinal,slKirillovMatrix_kronecker _ _ i₀ _
    (genericAffineSquare_degree K _ _) (genericAffineRows_degree K _ _) hfinal ?_⟩
  rw [slChartInput_card]
  norm_num [SLInput]

end FD56
