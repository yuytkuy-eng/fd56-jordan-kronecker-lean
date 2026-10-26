/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.TwoOutputOddSL

/-! The five-state SL classification is the depth-two case of the odd-state family. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K : Type*} [Field K]

theorem generic_five_two_sl_kirillov_minimal_degrees (i₀ : Fin 5) :
    HasMinimalKernelDegrees (slKirillovMatrix (genericAffineSquare K (Fin 5) (Fin 2))
      (genericAffineRows K (Fin 5) (Fin 2)) i₀) [8,8] := by
  simpa using generic_two_output_odd_sl_kirillov_minimal_degrees (K := K) 2 (by decide) i₀

theorem generic_five_two_sl_minimal_degrees (i₀ : Fin 5) :
    HasMinimalKernelDegrees (slEquationMatrix (genericAffineSquare K (Fin 5) (Fin 2))
      (genericAffineRows K (Fin 5) (Fin 2)) i₀) [8,8] := by
  simpa using generic_two_output_odd_sl_minimal_degrees (K := K) 2 (by decide) i₀

theorem generic_five_two_sl_hilbert (d : ℕ) :
    slHilbert (genericAffineSquare K (Fin 5) (Fin 2))
      (genericAffineRows K (Fin 5) (Fin 2)) d=2*(d-7) := by
  simpa using generic_two_output_odd_sl_hilbert (K := K) 2 (by decide) d

theorem generic_five_two_slHilbert_seven_zero :
    slHilbert (genericAffineSquare K (Fin 5) (Fin 2))
      (genericAffineRows K (Fin 5) (Fin 2)) 7=0 := by
  simp [generic_five_two_sl_hilbert]

theorem generic_five_two_sl_kirillov_hilbert_seven_zero (i₀ : Fin 5) :
    Module.finrank (AffineCoefficientField K (MatrixParameters (Fin 5) (Fin 2)))
      (polynomialKernelAtDegree (slKirillovMatrix (genericAffineSquare K (Fin 5) (Fin 2))
        (genericAffineRows K (Fin 5) (Fin 2)) i₀) 7)=0 := by
  rw [(hasMinimalKernelDegrees_iff_hilbert _ _).mp
    (generic_five_two_sl_kirillov_minimal_degrees i₀) 7]
  simp

theorem generic_five_two_sl_minimal_degrees_unique (i₀ : Fin 5) (xs : List ℕ)
    (hmin : HasMinimalKernelDegrees (slKirillovMatrix
      (genericAffineSquare K (Fin 5) (Fin 2)) (genericAffineRows K (Fin 5) (Fin 2)) i₀) xs) :
    xs=[8,8] := by
  have hp : xs.Perm (List.replicate 2 8) := by
    apply listHilbert_determines_indices
    intro d
    rw [listHilbert_nat,listHilbert_nat]
    exact_mod_cast ((hasMinimalKernelDegrees_iff_hilbert _ _).mp hmin d).symm.trans
      ((hasMinimalKernelDegrees_iff_hilbert _ _).mp
        (generic_five_two_sl_kirillov_minimal_degrees i₀) d)
  exact List.perm_replicate.mp hp

theorem generic_five_two_sl_kronecker_decomposition (i₀ : Fin 5) :
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K (Fin 5) (Fin 2)) (genericAffineRows K (Fin 5) (Fin 2)) i₀) [8,8] := by
  simpa using generic_two_output_odd_sl_all_depths (K := K) 2 i₀

end FD56
