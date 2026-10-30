/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputTripleSeedTransfer
import FD56.Hilbert.GenericSixOutputTripleSLTangentCriterion

/-! Two finite normalized three-column seed tests determine the actual
generic SL list after any number of certified degree-five splices. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K : Type*} [Field K] [CharZero K]

theorem generic_six_output_triple_sl_classification_of_seed
    (q a t : ℕ) (hq : 0<q) (hweight : (q+1)^2=a+5*t) (i₀ : Fin (6*q+3))
    (G₀ : Matrix (Fin 6) (Fin 3) K[X])
    (hG₀ : ∀ i j, (G₀ i j).coeff 0=sixOutputTripleBaseFrame K i j)
    (hdG₀ : ∀ i j, (G₀ i j).natDegree≤a) (hseedpos : 0<12*a/10)
    (hzero : Module.finrank K (polynomialKernelAtDegree
      (sixOutputTriplePluckerTangent (sixOutputTriplePluckerMinors G₀)) (12*a/10-1))=0)
    (hcritical : Module.finrank K (polynomialKernelAtDegree
      (sixOutputTriplePluckerTangent (sixOutputTriplePluckerMinors G₀)) (12*a/10))≤10-(12*a)%10) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (6*q+3)) (Fin 6))
      (genericAffineRows K (Fin (6*q+3)) (Fin 6)) i₀)
      (balancedDegreeList (10*(interiorFullWeight 3 3 q-1)-4*interiorFullWeight 3 3 q) 10) ∧
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K (Fin (6*q+3)) (Fin 6))
      (genericAffineRows K (Fin (6*q+3)) (Fin 6)) i₀)
      (balancedDegreeList (10*(interiorFullWeight 3 3 q-1)-4*interiorFullWeight 3 3 q) 10) := by
  have hW := six_output_triple_weight q
  have hindex : 4*interiorFullWeight 3 3 q/10=12*a/10+6*t := by omega
  have hlow : 4*interiorFullWeight 3 3 q/10-1=(12*a/10-1)+6*t := by omega
  have hmod : (4*interiorFullWeight 3 3 q)%10=(12*a)%10 := by omega
  apply generic_six_output_triple_sl_classification_of_tangent_tests (K:=K) q hq i₀
  · have h := generic_six_output_triple_tangent_kernel_finrank_le_seed
      q a t hq hweight G₀ hG₀ hdG₀ (12*a/10-1)
    rw [hzero,←hlow] at h
    exact Nat.eq_zero_of_le_zero h
  · have h := generic_six_output_triple_tangent_kernel_finrank_le_seed
      q a t hq hweight G₀ hG₀ hdG₀ (12*a/10)
    rw [←hindex] at h
    rw [hmod]
    exact h.trans hcritical

end FD56
