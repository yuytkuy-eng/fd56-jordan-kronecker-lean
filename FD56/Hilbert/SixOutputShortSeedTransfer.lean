/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.NormalizedSixOutputShortIteration
import FD56.Hilbert.GenericSixOutputTangentTransfer
import FD56.Hilbert.GenericSixOutputCorankTwoTangentTransfer

/-! The short normalized splice transfers finite seed bounds to the actual
generic six-output two-column and corank-two tangent kernels. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K : Type*} [Field K] [CharZero K]

theorem generic_six_output_tangent_kernel_finrank_le_short_seed
    (q a b t : ℕ) (hq : 0<q) (hab : b=a ∨ b=a+1)
    (hweight : twoColumnInteriorWeight 4 q=a+b+6*t)
    (u₀ v₀ : Fin 6 → K[X])
    (hu₀ : ∀ i, (u₀ i).coeff 0=(![1,0,0,0,0,0] : Fin 6 → K) i)
    (hv₀ : ∀ i, (v₀ i).coeff 0=(![0,-1,0,0,0,0] : Fin 6 → K) i)
    (hdu₀ : ∀ i, (u₀ i).natDegree≤a) (hdv₀ : ∀ i, (v₀ i).natDegree≤b) (d : ℕ) :
    Module.finrank (AffineCoefficientField K (MatrixParameters (Fin (6*q+2)) (Fin 6)))
      (polynomialKernelAtDegree (sixOutputPluckerTangent (genericTwoColumnInteriorMinors (K:=K) 4 q)) (d+2*t)) ≤
      Module.finrank K (polynomialKernelAtDegree
        (sixOutputPluckerTangent (twoColumnWedge u₀ v₀)) d) := by
  obtain ⟨E,fieldE,charE,σ,w,z,_,_,hdw,hdz,hbound⟩ :=
    normalized_six_output_short_splice_iterate u₀ v₀ a b hu₀ hv₀ hdu₀ hdv₀ t
  letI := fieldE
  letI := charE
  letI := σ.toAlgebra
  have h := generic_six_output_tangent_kernel_finrank_le_field_witness
    (K:=K) q (a+3*t) (b+3*t) (d+2*t) hq (by omega) (by omega) w z hdw hdz
  exact h.trans (hbound d)

theorem generic_six_output_corank_two_tangent_kernel_finrank_le_short_seed
    (q a b t : ℕ) (hq : 0<q) (hab : b=a ∨ b=a+1)
    (hweight : interiorFullWeight 4 2 q=a+b+6*t)
    (u₀ v₀ : Fin 6 → K[X])
    (hu₀ : ∀ i, (u₀ i).coeff 0=(![1,0,0,0,0,0] : Fin 6 → K) i)
    (hv₀ : ∀ i, (v₀ i).coeff 0=(![0,-1,0,0,0,0] : Fin 6 → K) i)
    (hdu₀ : ∀ i, (u₀ i).natDegree≤a) (hdv₀ : ∀ i, (v₀ i).natDegree≤b) (d : ℕ) :
    Module.finrank (AffineCoefficientField K (MatrixParameters (Fin (6*q+4)) (Fin 6)))
      (polynomialKernelAtDegree (sixOutputPluckerTangent (genericSixOutputCorankTwoMinors (K:=K) q)) (d+2*t)) ≤
      Module.finrank K (polynomialKernelAtDegree
        (sixOutputPluckerTangent (twoColumnWedge u₀ v₀)) d) := by
  obtain ⟨E,fieldE,charE,σ,w,z,_,_,hdw,hdz,hbound⟩ :=
    normalized_six_output_short_splice_iterate u₀ v₀ a b hu₀ hv₀ hdu₀ hdv₀ t
  letI := fieldE
  letI := charE
  letI := σ.toAlgebra
  have h := generic_six_output_corank_two_tangent_kernel_finrank_le_field_witness
    (K:=K) q (a+3*t) (b+3*t) (d+2*t) hq (by omega) (by omega) w z hdw hdz
  exact h.trans (hbound d)

end FD56
