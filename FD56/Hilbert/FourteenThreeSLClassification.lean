/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.FourteenThreeBaseStructure
import FD56.Hilbert.FourteenThreeGenericScalarLifts
import FD56.Hilbert.MinimalDegreeFrameBound

/-! The complete generic SL decomposition for fourteen states and three outputs. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K : Type*} [Field K] [CharZero K]

theorem generic_fourteen_three_sl_minimal_degrees (i₀ : Fin 14) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin 14) (Fin 3)) (genericAffineRows K (Fin 14) (Fin 3)) i₀)
      [39,39,39] := by
  obtain ⟨xs,hlen,hsum,hmin,_⟩ := generic_fourteen_three_base_sl_kronecker_structure (K:=K) i₀
  obtain ⟨Z,hAZ,hZ,hinj⟩ := generic_fourteen_three_sl_kernel_frame (K:=K) i₀
  exact minimal_degrees_uniform_of_full_frame_at_point _ xs hmin 3 39 Z hlen
    (by omega) hAZ hZ 0 hinj

theorem generic_fourteen_three_sl_kronecker_decomposition (i₀ : Fin 14) :
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K (Fin 14) (Fin 3)) (genericAffineRows K (Fin 14) (Fin 3)) i₀)
      [39,39,39] := by
  apply slKirillovMatrix_kronecker _ _ i₀ _
    (genericAffineSquare_degree K _ _) (genericAffineRows_degree K _ _)
    (generic_fourteen_three_sl_minimal_degrees i₀)
  rw [slChartInput_card]
  norm_num [SLInput]

theorem generic_fourteen_three_sl_hilbert (d : ℕ) :
    slHilbert (genericAffineSquare K (Fin 14) (Fin 3))
      (genericAffineRows K (Fin 14) (Fin 3)) d=3*(d+1-39) := by
  rw [slHilbert_eq_matrix_kernel _ _ (0 : Fin 14),
    (hasMinimalKernelDegrees_iff_hilbert _ _).mp (generic_fourteen_three_sl_minimal_degrees 0)]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
  omega

end FD56
