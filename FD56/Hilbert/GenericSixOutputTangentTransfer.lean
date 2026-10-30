/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputTangentExtensionTransfer
import FD56.Hilbert.GenericTwoColumnFullSpecialization

/-! Extension-valued bounded columns control the actual generic six-output,
remainder-two tangent kernel through faithful minor specialization. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K E : Type*} [Field K] [CharZero K] [Field E] [Algebra K E]

theorem generic_six_output_tangent_kernel_finrank_le_field_witness
    (q a b d : ℕ) (hq : 0<q) (hab : b=a ∨ b=a+1)
    (hweight : twoColumnInteriorWeight 4 q=a+b)
    (u₀ v₀ : Fin 6 → E[X])
    (hdu₀ : ∀ i, (u₀ i).natDegree≤a) (hdv₀ : ∀ i, (v₀ i).natDegree≤b) :
    Module.finrank (AffineCoefficientField K (MatrixParameters (Fin (6*q+2)) (Fin 6)))
      (polynomialKernelAtDegree
        (sixOutputPluckerTangent (genericTwoColumnInteriorMinors (K:=K) 4 q)) d) ≤
      Module.finrank E (polynomialKernelAtDegree
        (sixOutputPluckerTangent (twoColumnWedge u₀ v₀)) d) := by
  obtain ⟨A,B,u,v,hAB,hsum,hu,hv,hF,hfaithful⟩ :=
    generic_two_column_full_specialization_faithful (K:=K) 4 q hq
  have hABsum : A+B=twoColumnInteriorWeight 4 q := by
    unfold twoColumnInteriorWeight
    norm_num only [Nat.reduceAdd] at hsum ⊢
    omega
  have hA : A=a := by omega
  have hB : B=b := by omega
  subst A
  subst B
  rw [hF]
  exact six_output_tangent_kernel_finrank_le_of_faithful_extension
    a b d u v hu hv hfaithful u₀ v₀ hdu₀ hdv₀

end FD56
