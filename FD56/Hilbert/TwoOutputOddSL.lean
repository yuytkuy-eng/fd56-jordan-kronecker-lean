/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.TwoOutputOddSLScalarCriterion
import FD56.Hilbert.TwoOutputOddSLNonzero

/-! Complete generic SL Kronecker decomposition for every positive odd depth and two outputs. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K : Type*} [Field K]

theorem generic_two_output_odd_sl_critical_vanishing (q : ℕ) (hq : 0<q) :
    slHilbert (genericAffineSquare K (Fin (2*q+1)) (Fin 2))
      (genericAffineRows K (Fin (2*q+1)) (Fin 2)) (q*(q+2)-1)=0 := by
  let M := genericAffineSquare K (Fin (2*q+1)) (Fin 2)
  let P := genericAffineRows K (Fin (2*q+1)) (Fin 2)
  have hM := genericAffineSquare_degree K (Fin (2*q+1)) (Fin 2)
  have hP := genericAffineRows_degree K (Fin (2*q+1)) (Fin 2)
  obtain ⟨hZ₀,hp₀⟩ := oddTwoScalarLift_degree q M P hM hP 0
  obtain ⟨hZ₁,hp₁⟩ := oddTwoScalarLift_degree q M P hM hP 1
  have hp : 0<q*(q+2) := Nat.mul_pos hq (by omega)
  have he : q*(q+2)-1+1=q*(q+2) := Nat.sub_add_cancel hp
  apply slHilbert_zero_of_scalar_lifts M P (0 : Fin (2*q+1)) (q*(q+2)-1) hM hP
    (oddTwoScalarLift q M P 0) (oddTwoScalarLift q M P 1)
    (oddTwoScalarValue q M P 0) (oddTwoScalarValue q M P 1)
    (oddTwoScalarLift_equation q M P 0) (oddTwoScalarLift_equation q M P 1)
  · simpa only [he] using hZ₀
  · simpa only [he] using hZ₁
  · exact hp₀.trans (by omega)
  · exact hp₁.trans (by omega)
  · exact generic_two_output_odd_scalar_cross_ne_zero q
  · exact generic_two_output_odd_gl_critical_vanishing q hq

theorem generic_two_output_odd_sl_kirillov_minimal_degrees
    (q : ℕ) (hq : 0<q) (i₀ : Fin (2*q+1)) :
    HasMinimalKernelDegrees (slKirillovMatrix
      (genericAffineSquare K (Fin (2*q+1)) (Fin 2))
      (genericAffineRows K (Fin (2*q+1)) (Fin 2)) i₀) [q*(q+2),q*(q+2)] :=
  generic_two_output_odd_sl_degrees_of_vanishing q hq i₀
    (generic_two_output_odd_sl_critical_vanishing q hq)

theorem generic_two_output_odd_sl_minimal_degrees
    (q : ℕ) (hq : 0<q) (i₀ : Fin (2*q+1)) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (2*q+1)) (Fin 2))
      (genericAffineRows K (Fin (2*q+1)) (Fin 2)) i₀) [q*(q+2),q*(q+2)] :=
  (slKirillovMatrix_hasMinimalKernelDegrees_iff _ _ _ _).mp
    (generic_two_output_odd_sl_kirillov_minimal_degrees q hq i₀)

theorem generic_two_output_odd_sl_hilbert (q : ℕ) (hq : 0<q) (d : ℕ) :
    slHilbert (genericAffineSquare K (Fin (2*q+1)) (Fin 2))
      (genericAffineRows K (Fin (2*q+1)) (Fin 2)) d=2*(d+1-q*(q+2)) := by
  rw [slHilbert_eq_matrix_kernel _ _ (0 : Fin (2*q+1)) d,
    (hasMinimalKernelDegrees_iff_hilbert _ _).mp (generic_two_output_odd_sl_minimal_degrees q hq 0)]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
  omega

theorem generic_two_output_odd_sl_kronecker_decomposition
    (q : ℕ) (hq : 0<q) (i₀ : Fin (2*q+1)) :
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K (Fin (2*q+1)) (Fin 2))
      (genericAffineRows K (Fin (2*q+1)) (Fin 2)) i₀) [q*(q+2),q*(q+2)] :=
  generic_two_output_odd_sl_kronecker_of_vanishing q hq i₀
    (generic_two_output_odd_sl_critical_vanishing q hq)

theorem generic_two_output_odd_sl_all_depths (q : ℕ) (i₀ : Fin (2*q+1)) :
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K (Fin (2*q+1)) (Fin 2))
      (genericAffineRows K (Fin (2*q+1)) (Fin 2)) i₀) [q*(q+2),q*(q+2)] := by
  cases q with
  | zero =>
    simpa [balancedDegreeList] using
      (generic_above_sl_kronecker_decomposition (K := K) (m := Fin 2) i₀ (by simp))
  | succ q => exact generic_two_output_odd_sl_kronecker_decomposition (q+1) (by omega) i₀

end FD56
