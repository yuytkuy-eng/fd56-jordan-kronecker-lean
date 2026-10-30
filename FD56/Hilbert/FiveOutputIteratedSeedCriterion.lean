/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.FiveOutputIteratedSeedTransfer
import FD56.Hilbert.GenericFiveOutputSLTangentCriterion
import FD56.Hilbert.GenericFiveOutputCorankTwoSLTangentCriterion

/-! Two finite normalized seed tests determine complete generic five-output
SL profiles in every weight obtained by adding multiples of fourteen.
The finite seed tests remain explicit hypotheses. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K : Type*} [Field K] [CharZero K]

theorem generic_five_output_sl_classification_of_iterated_seed
    (q a b t : ℕ) (hq : 0<q) (hab : b=a ∨ b=a+1)
    (hweight : (twoColumnInteriorWeight 3 q)=a+b+14*t) (i₀ : Fin (5*q+2))
    (u₀ v₀ : Fin 5 → K[X])
    (hu₀ : ∀ i, (u₀ i).coeff 0=(![1,0,0,0,0] : Fin 5 → K) i)
    (hv₀ : ∀ i, (v₀ i).coeff 0=(![0,-1,0,0,0] : Fin 5 → K) i)
    (hdu₀ : ∀ i, (u₀ i).natDegree≤a) (hdv₀ : ∀ i, (v₀ i).natDegree≤b)
    (hseedpos : 0<2*(a+b)/7)
    (hzero : Module.finrank K (polynomialKernelAtDegree
      (fiveOutputPluckerTangent (twoColumnWedge u₀ v₀)) (2*(a+b)/7-1))=0)
    (hcritical : Module.finrank K (polynomialKernelAtDegree
      (fiveOutputPluckerTangent (twoColumnWedge u₀ v₀)) (2*(a+b)/7))≤7-(2*(a+b))%7) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (5*q+2)) (Fin 5))
      (genericAffineRows K (Fin (5*q+2)) (Fin 5)) i₀)
      (balancedDegreeList (7*((twoColumnInteriorWeight 3 q)-1)-2*(twoColumnInteriorWeight 3 q)) 7) ∧
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K (Fin (5*q+2)) (Fin 5))
      (genericAffineRows K (Fin (5*q+2)) (Fin 5)) i₀)
      (balancedDegreeList (7*((twoColumnInteriorWeight 3 q)-1)-2*(twoColumnInteriorWeight 3 q)) 7) := by
  have hindex : 2*(twoColumnInteriorWeight 3 q)/7=2*(a+b)/7+4*t := by omega
  have hlow : 2*(twoColumnInteriorWeight 3 q)/7-1=(2*(a+b)/7-1)+4*t := by omega
  have hmod : (2*(twoColumnInteriorWeight 3 q))%7=(2*(a+b))%7 := by omega
  apply generic_five_output_sl_classification_of_tangent_tests (K:=K) q hq i₀
  · have h := generic_five_output_tangent_kernel_finrank_le_iterated_seed
      q a b t hq hab hweight u₀ v₀ hu₀ hv₀ hdu₀ hdv₀ (2*(a+b)/7-1)
    rw [hzero,←hlow] at h
    exact Nat.eq_zero_of_le_zero h
  · have h := generic_five_output_tangent_kernel_finrank_le_iterated_seed
      q a b t hq hab hweight u₀ v₀ hu₀ hv₀ hdu₀ hdv₀ (2*(a+b)/7)
    rw [←hindex] at h
    rw [hmod]
    exact h.trans hcritical

theorem generic_five_output_corank_two_sl_classification_of_iterated_seed
    (q a b t : ℕ) (hq : 0<q) (hab : b=a ∨ b=a+1)
    (hweight : (interiorFullWeight 3 2 q)=a+b+14*t) (i₀ : Fin (5*q+3))
    (u₀ v₀ : Fin 5 → K[X])
    (hu₀ : ∀ i, (u₀ i).coeff 0=(![1,0,0,0,0] : Fin 5 → K) i)
    (hv₀ : ∀ i, (v₀ i).coeff 0=(![0,-1,0,0,0] : Fin 5 → K) i)
    (hdu₀ : ∀ i, (u₀ i).natDegree≤a) (hdv₀ : ∀ i, (v₀ i).natDegree≤b)
    (hseedpos : 0<2*(a+b)/7)
    (hzero : Module.finrank K (polynomialKernelAtDegree
      (fiveOutputPluckerTangent (twoColumnWedge u₀ v₀)) (2*(a+b)/7-1))=0)
    (hcritical : Module.finrank K (polynomialKernelAtDegree
      (fiveOutputPluckerTangent (twoColumnWedge u₀ v₀)) (2*(a+b)/7))≤7-(2*(a+b))%7) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (5*q+3)) (Fin 5))
      (genericAffineRows K (Fin (5*q+3)) (Fin 5)) i₀)
      (balancedDegreeList (7*((interiorFullWeight 3 2 q)-1)-2*(interiorFullWeight 3 2 q)) 7) ∧
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K (Fin (5*q+3)) (Fin 5))
      (genericAffineRows K (Fin (5*q+3)) (Fin 5)) i₀)
      (balancedDegreeList (7*((interiorFullWeight 3 2 q)-1)-2*(interiorFullWeight 3 2 q)) 7) := by
  have hindex : 2*(interiorFullWeight 3 2 q)/7=2*(a+b)/7+4*t := by omega
  have hlow : 2*(interiorFullWeight 3 2 q)/7-1=(2*(a+b)/7-1)+4*t := by omega
  have hmod : (2*(interiorFullWeight 3 2 q))%7=(2*(a+b))%7 := by omega
  apply generic_five_output_corank_two_sl_classification_of_tangent_tests (K:=K) q hq i₀
  · have h := generic_five_output_corank_two_tangent_kernel_finrank_le_iterated_seed
      q a b t hq hab hweight u₀ v₀ hu₀ hv₀ hdu₀ hdv₀ (2*(a+b)/7-1)
    rw [hzero,←hlow] at h
    exact Nat.eq_zero_of_le_zero h
  · have h := generic_five_output_corank_two_tangent_kernel_finrank_le_iterated_seed
      q a b t hq hab hweight u₀ v₀ hu₀ hv₀ hdu₀ hdv₀ (2*(a+b)/7)
    rw [←hindex] at h
    rw [hmod]
    exact h.trans hcritical

end FD56
