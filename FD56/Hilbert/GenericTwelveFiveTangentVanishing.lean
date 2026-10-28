/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericTwoColumnFullSpecialization
import FD56.Hilbert.FiveOutputTangentVanishing
import FD56.LinearAlgebra.FiveOutputTangentTransfer

/-! The actual generic twelve-state, five-output Plucker tangent has no
nonzero polynomial kernel vector of degree at most five. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxHeartbeats 2000000

variable {K : Type*} [Field K] [CharZero K]

private abbrev TwelveFiveField :=
  AffineCoefficientField K (MatrixParameters (Fin 12) (Fin 5))

theorem generic_twelve_five_tangent_coefficient_injective :
    Function.Injective (selectedPolynomialCoefficientMatrix
      (fiveOutputPluckerTangent (genericTwoColumnInteriorMinors (K:=K) 3 2))
      5 fiveOutputTangentCoefficientRows).mulVec := by
  obtain ⟨a,b,u,v,hab,hsum,hu,hv,hF,hfaithful⟩ :=
    generic_two_column_full_specialization_faithful (K:=K) 3 2 (by decide)
  have ha : a=10 := by omega
  have hb : b=11 := by omega
  subst a
  subst b
  rw [hF]
  apply five_output_tangent_coefficients_injective_of_faithful
    10 11 5 fiveOutputTangentCoefficientRows u v hu hv hfaithful
    (fiveOutputTangentU (R:=K)) (fiveOutputTangentV (R:=K))
    (fiveOutputTangentU_degree (R:=K)) (fiveOutputTangentV_degree (R:=K))
  exact fiveOutputTangent_coefficient_injective_charZero

theorem generic_twelve_five_tangent_bounded_kernel_zero
    (z : Fin 10 → (TwelveFiveField (K:=K))[X])
    (hz : fiveOutputPluckerTangent (genericTwoColumnInteriorMinors (K:=K) 3 2)*ᵥz=0)
    (hdeg : ∀ j, (z j).natDegree≤5) : z=0 :=
  bounded_kernel_zero_of_selected_coefficient_injective
    (fiveOutputPluckerTangent (genericTwoColumnInteriorMinors (K:=K) 3 2))
    5 fiveOutputTangentCoefficientRows generic_twelve_five_tangent_coefficient_injective z hz hdeg

end FD56
