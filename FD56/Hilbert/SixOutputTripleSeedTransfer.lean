/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.NormalizedSixOutputTripleIteration
import FD56.Hilbert.GenericSixOutputTripleTangentTransfer

/-! The normalized degree-five recurrence transfers finite seed bounds to
the actual generic six-output middle-remainder tangent kernel. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K : Type*} [Field K] [CharZero K]

theorem generic_six_output_triple_tangent_kernel_finrank_le_seed
    (q a t : ℕ) (hq : 0<q) (hweight : (q+1)^2=a+5*t)
    (G₀ : Matrix (Fin 6) (Fin 3) K[X])
    (hG₀ : ∀ i j, (G₀ i j).coeff 0=sixOutputTripleBaseFrame K i j)
    (hdG₀ : ∀ i j, (G₀ i j).natDegree≤a) (d : ℕ) :
    Module.finrank (AffineCoefficientField K (MatrixParameters (Fin (6*q+3)) (Fin 6)))
      (polynomialKernelAtDegree
        (sixOutputTriplePluckerTangent (genericSixOutputTripleMinors (K:=K) q)) (d+6*t)) ≤
      Module.finrank K (polynomialKernelAtDegree
        (sixOutputTriplePluckerTangent (sixOutputTriplePluckerMinors G₀)) d) := by
  obtain ⟨E,fieldE,charE,σ,G,_,hdG,hbound⟩ :=
    normalized_six_output_triple_splice_iterate G₀ a hG₀ hdG₀ t
  letI := fieldE
  letI := charE
  letI := σ.toAlgebra
  have h := generic_six_output_triple_tangent_kernel_finrank_le_field_witness
    (K:=K) q (d+6*t) hq G (by simpa only [hweight] using hdG)
  exact h.trans (hbound d)

end FD56
