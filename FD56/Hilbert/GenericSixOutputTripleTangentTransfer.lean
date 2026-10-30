/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputTripleTangentExtensionTransfer
import FD56.Hilbert.GenericSixOutputTripleSpecialization
import FD56.Hilbert.SixOutputTripleGradients

/-! Every extension-valued equal-degree frame bounds the bounded tangent
kernel of the actual six-output middle-remainder minors. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K E : Type*} [Field K] [CharZero K] [Field E] [Algebra K E]

theorem generic_six_output_triple_tangent_kernel_finrank_le_field_witness
    (q d : ℕ) (hq : 0<q) (G₀ : Matrix (Fin 6) (Fin 3) E[X])
    (hG₀ : ∀ i j, (G₀ i j).natDegree≤(q+1)^2) :
    Module.finrank (AffineCoefficientField K (MatrixParameters (Fin (6*q+3)) (Fin 6)))
      (polynomialKernelAtDegree
        (sixOutputTriplePluckerTangent (genericSixOutputTripleMinors (K:=K) q)) d) ≤
      Module.finrank E (polynomialKernelAtDegree
        (sixOutputTriplePluckerTangent (sixOutputTriplePluckerMinors G₀)) d) := by
  obtain ⟨G,hG,hfull,hfaithful⟩ := generic_six_output_triple_specialization_faithful (K:=K) q hq
  have he : genericSixOutputTripleMinors (K:=K) q=sixOutputTriplePluckerMinors G := by
    funext i
    exact hfull (sixOutputTriple i)
  rw [he]
  exact six_output_triple_tangent_kernel_finrank_le_of_faithful_extension
    ((q+1)^2) d G hG hfaithful G₀ hG₀

end FD56
