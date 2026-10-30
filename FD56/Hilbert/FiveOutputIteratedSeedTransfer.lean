/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.NormalizedFiveOutputIteration
import FD56.Hilbert.FiveOutputTangentExtensionTransfer
import FD56.Hilbert.GenericTwoColumnFullSpecialization
import FD56.Hilbert.GenericFiveOutputCorankTwoSpecialization

/-! Normalized seeds control the actual generic five-output tangent kernels
at every nonnegative splice depth, for both interior remainders. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra K L]

theorem five_output_tangent_kernel_finrank_le_iterated_seed
    (a b t : ℕ) (u v : Fin 5 → L[X])
    (hu : ∀ i, (u i).natDegree≤a+7*t) (hv : ∀ i, (v i).natDegree≤b+7*t)
    (hfaithful : Function.Injective (twoColumnMinorSpecialization (a+7*t) (b+7*t)
      (twoColumnCoefficientEvaluation (K:=K) (a+7*t) (b+7*t) u v)))
    (u₀ v₀ : Fin 5 → K[X])
    (hu₀ : ∀ i, (u₀ i).coeff 0=(![1,0,0,0,0] : Fin 5 → K) i)
    (hv₀ : ∀ i, (v₀ i).coeff 0=(![0,-1,0,0,0] : Fin 5 → K) i)
    (hdu₀ : ∀ i, (u₀ i).natDegree≤a) (hdv₀ : ∀ i, (v₀ i).natDegree≤b) (d : ℕ) :
    Module.finrank L (polynomialKernelAtDegree
      (fiveOutputPluckerTangent (twoColumnWedge u v)) (d+4*t)) ≤
      Module.finrank K (polynomialKernelAtDegree
        (fiveOutputPluckerTangent (twoColumnWedge u₀ v₀)) d) := by
  obtain ⟨E,fieldE,charE,σ,w,z,_,_,hdw,hdz,hbound⟩ :=
    normalized_five_output_splice_iterate u₀ v₀ a b hu₀ hv₀ hdu₀ hdv₀ t
  letI := fieldE
  letI := charE
  letI := σ.toAlgebra
  exact (five_output_tangent_kernel_finrank_le_of_faithful_extension
    (a+7*t) (b+7*t) (d+4*t) u v hu hv hfaithful w z hdw hdz).trans (hbound d)

theorem generic_five_output_tangent_kernel_finrank_le_iterated_seed
    (q a b t : ℕ) (hq : 0<q) (hab : b=a ∨ b=a+1)
    (hweight : twoColumnInteriorWeight 3 q=a+b+14*t)
    (u₀ v₀ : Fin 5 → K[X])
    (hu₀ : ∀ i, (u₀ i).coeff 0=(![1,0,0,0,0] : Fin 5 → K) i)
    (hv₀ : ∀ i, (v₀ i).coeff 0=(![0,-1,0,0,0] : Fin 5 → K) i)
    (hdu₀ : ∀ i, (u₀ i).natDegree≤a) (hdv₀ : ∀ i, (v₀ i).natDegree≤b) (d : ℕ) :
    Module.finrank (AffineCoefficientField K (MatrixParameters (Fin (5*q+2)) (Fin 5)))
      (polynomialKernelAtDegree
        (fiveOutputPluckerTangent (genericTwoColumnInteriorMinors (K:=K) 3 q)) (d+4*t)) ≤
      Module.finrank K (polynomialKernelAtDegree
        (fiveOutputPluckerTangent (twoColumnWedge u₀ v₀)) d) := by
  obtain ⟨A,B,u,v,hAB,hsum,hu,hv,hF,hfaithful⟩ :=
    generic_two_column_full_specialization_faithful (K:=K) 3 q hq
  have hABsum : A+B=twoColumnInteriorWeight 3 q := by
    unfold twoColumnInteriorWeight
    norm_num only [Nat.reduceAdd] at hsum ⊢
    omega
  have hA : A=a+7*t := by omega
  have hB : B=b+7*t := by omega
  subst A
  subst B
  rw [hF]
  exact five_output_tangent_kernel_finrank_le_iterated_seed
    a b t u v hu hv hfaithful u₀ v₀ hu₀ hv₀ hdu₀ hdv₀ d

theorem generic_five_output_corank_two_tangent_kernel_finrank_le_iterated_seed
    (q a b t : ℕ) (hq : 0<q) (hab : b=a ∨ b=a+1)
    (hweight : interiorFullWeight 3 2 q=a+b+14*t)
    (u₀ v₀ : Fin 5 → K[X])
    (hu₀ : ∀ i, (u₀ i).coeff 0=(![1,0,0,0,0] : Fin 5 → K) i)
    (hv₀ : ∀ i, (v₀ i).coeff 0=(![0,-1,0,0,0] : Fin 5 → K) i)
    (hdu₀ : ∀ i, (u₀ i).natDegree≤a) (hdv₀ : ∀ i, (v₀ i).natDegree≤b) (d : ℕ) :
    Module.finrank (AffineCoefficientField K (MatrixParameters (Fin (5*q+3)) (Fin 5)))
      (polynomialKernelAtDegree
        (fiveOutputPluckerTangent (genericFiveOutputCorankTwoMinors (K:=K) q)) (d+4*t)) ≤
      Module.finrank K (polynomialKernelAtDegree
        (fiveOutputPluckerTangent (twoColumnWedge u₀ v₀)) d) := by
  obtain ⟨A,B,u,v,hAB,hsum,hu,hv,hF,hfaithful⟩ :=
    generic_five_output_corank_two_full_specialization_faithful (K:=K) q hq
  have hA : A=a+7*t := by omega
  have hB : B=b+7*t := by omega
  subst A
  subst B
  rw [hF]
  exact five_output_tangent_kernel_finrank_le_iterated_seed
    a b t u v hu hv hfaithful u₀ v₀ hu₀ hv₀ hdu₀ hdv₀ d

end FD56
