/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputShortSeedTransfer
import FD56.Hilbert.GenericSixOutputSLTangentCriterion
import FD56.Hilbert.GenericSixOutputCorankTwoSLTangentCriterion

/-! Two finite normalized seed tests determine generic six-output SL lists
at all weights obtained by repeatedly adding six. The tests remain premises. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K : Type*} [Field K] [CharZero K]

theorem generic_six_output_sl_classification_of_short_seed
    (q a b t : ℕ) (hq : 0<q) (hab : b=a ∨ b=a+1)
    (hweight : (twoColumnInteriorWeight 4 q)=a+b+6*t) (i₀ : Fin (6*q+2))
    (u₀ v₀ : Fin 6 → K[X])
    (hu₀ : ∀ i, (u₀ i).coeff 0=(![1,0,0,0,0,0] : Fin 6 → K) i)
    (hv₀ : ∀ i, (v₀ i).coeff 0=(![0,-1,0,0,0,0] : Fin 6 → K) i)
    (hdu₀ : ∀ i, (u₀ i).natDegree≤a) (hdv₀ : ∀ i, (v₀ i).natDegree≤b)
    (hseedpos : 0<3*(a+b)/9)
    (hzero : Module.finrank K (polynomialKernelAtDegree
      (sixOutputPluckerTangent (twoColumnWedge u₀ v₀)) (3*(a+b)/9-1))=0)
    (hcritical : Module.finrank K (polynomialKernelAtDegree
      (sixOutputPluckerTangent (twoColumnWedge u₀ v₀)) (3*(a+b)/9))≤9-(3*(a+b))%9) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (6*q+2)) (Fin 6))
      (genericAffineRows K (Fin (6*q+2)) (Fin 6)) i₀)
      (balancedDegreeList (9*((twoColumnInteriorWeight 4 q)-1)-3*(twoColumnInteriorWeight 4 q)) 9) ∧
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K (Fin (6*q+2)) (Fin 6))
      (genericAffineRows K (Fin (6*q+2)) (Fin 6)) i₀)
      (balancedDegreeList (9*((twoColumnInteriorWeight 4 q)-1)-3*(twoColumnInteriorWeight 4 q)) 9) := by
  have hindex : 3*(twoColumnInteriorWeight 4 q)/9=3*(a+b)/9+2*t := by omega
  have hlow : 3*(twoColumnInteriorWeight 4 q)/9-1=(3*(a+b)/9-1)+2*t := by omega
  have hmod : (3*(twoColumnInteriorWeight 4 q))%9=(3*(a+b))%9 := by omega
  apply generic_six_output_sl_classification_of_tangent_tests (K:=K) q hq i₀
  · have h := generic_six_output_tangent_kernel_finrank_le_short_seed
      q a b t hq hab hweight u₀ v₀ hu₀ hv₀ hdu₀ hdv₀ (3*(a+b)/9-1)
    rw [hzero,←hlow] at h
    exact Nat.eq_zero_of_le_zero h
  · have h := generic_six_output_tangent_kernel_finrank_le_short_seed
      q a b t hq hab hweight u₀ v₀ hu₀ hv₀ hdu₀ hdv₀ (3*(a+b)/9)
    rw [←hindex] at h
    rw [hmod]
    exact h.trans hcritical

theorem generic_six_output_corank_two_sl_classification_of_short_seed
    (q a b t : ℕ) (hq : 0<q) (hab : b=a ∨ b=a+1)
    (hweight : (interiorFullWeight 4 2 q)=a+b+6*t) (i₀ : Fin (6*q+4))
    (u₀ v₀ : Fin 6 → K[X])
    (hu₀ : ∀ i, (u₀ i).coeff 0=(![1,0,0,0,0,0] : Fin 6 → K) i)
    (hv₀ : ∀ i, (v₀ i).coeff 0=(![0,-1,0,0,0,0] : Fin 6 → K) i)
    (hdu₀ : ∀ i, (u₀ i).natDegree≤a) (hdv₀ : ∀ i, (v₀ i).natDegree≤b)
    (hseedpos : 0<3*(a+b)/9)
    (hzero : Module.finrank K (polynomialKernelAtDegree
      (sixOutputPluckerTangent (twoColumnWedge u₀ v₀)) (3*(a+b)/9-1))=0)
    (hcritical : Module.finrank K (polynomialKernelAtDegree
      (sixOutputPluckerTangent (twoColumnWedge u₀ v₀)) (3*(a+b)/9))≤9-(3*(a+b))%9) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (6*q+4)) (Fin 6))
      (genericAffineRows K (Fin (6*q+4)) (Fin 6)) i₀)
      (balancedDegreeList (9*((interiorFullWeight 4 2 q)-1)-3*(interiorFullWeight 4 2 q)) 9) ∧
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K (Fin (6*q+4)) (Fin 6))
      (genericAffineRows K (Fin (6*q+4)) (Fin 6)) i₀)
      (balancedDegreeList (9*((interiorFullWeight 4 2 q)-1)-3*(interiorFullWeight 4 2 q)) 9) := by
  have hindex : 3*(interiorFullWeight 4 2 q)/9=3*(a+b)/9+2*t := by omega
  have hlow : 3*(interiorFullWeight 4 2 q)/9-1=(3*(a+b)/9-1)+2*t := by omega
  have hmod : (3*(interiorFullWeight 4 2 q))%9=(3*(a+b))%9 := by omega
  apply generic_six_output_corank_two_sl_classification_of_tangent_tests (K:=K) q hq i₀
  · have h := generic_six_output_corank_two_tangent_kernel_finrank_le_short_seed
      q a b t hq hab hweight u₀ v₀ hu₀ hv₀ hdu₀ hdv₀ (3*(a+b)/9-1)
    rw [hzero,←hlow] at h
    exact Nat.eq_zero_of_le_zero h
  · have h := generic_six_output_corank_two_tangent_kernel_finrank_le_short_seed
      q a b t hq hab hweight u₀ v₀ hu₀ hv₀ hdu₀ hdv₀ (3*(a+b)/9)
    rw [←hindex] at h
    rw [hmod]
    exact h.trans hcritical

end FD56
