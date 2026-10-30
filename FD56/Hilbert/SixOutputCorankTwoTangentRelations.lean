/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericSixOutputCorankTwoSpecialization

/-! The fifteen Plucker tangent equations annihilate the actual signed
observability gradients in the six-output corank-two range. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxHeartbeats 2000000

variable {K : Type*} [Field K] [CharZero K]

theorem generic_six_output_corank_two_minors_plucker (q : ℕ) (hq : 0<q)
    (i j k l : Fin 6) :
    pluckerQuadraticRelation (genericSixOutputCorankTwoMinors (K:=K) q) i j k l=0 := by
  obtain ⟨a,b,u,v,_,_,_,_,hF,_⟩ :=
    generic_six_output_corank_two_full_specialization_faithful (K:=K) q hq
  rw [hF]
  simpa only [one_smul] using scaled_wedge_plucker_relation
    (1 : (AffineCoefficientField K (MatrixParameters (Fin (6*q+4)) (Fin 6)))[X]) u v i j k l

theorem generic_six_output_corank_two_gradient_tangent (q : ℕ) (hq : 0<q) :
    sixOutputPluckerTangent (genericSixOutputCorankTwoMinors (K:=K) q) *
      (genericSixOutputCorankTwoGradients (K:=K) q).transpose=0 := by
  funext i t
  obtain ⟨D,hD⟩ := generic_six_output_corank_two_gradient_derivation (K:=K) q t
  have hp (j : Fin 15) : polynomialCoefficientDerivation D
      (sixOutputCorankTwoMinor q (genericAffineSquare K _ _) (genericAffineRows K _ _) j)=
        genericSixOutputCorankTwoGradients (K:=K) q t j := by
    simpa only [genericSixOutputCorankTwoMinors,sixOutputCorankTwoMinors,
      sixOutputAlternatingMatrix_upper] using hD j
  let H := sixOutputAlternatingMatrix (genericSixOutputCorankTwoGradients (K:=K) q t)
  have he : (fun a b => polynomialCoefficientDerivation D
      (genericSixOutputCorankTwoMinors (K:=K) q a b))=H := by
    funext a b
    fin_cases a <;> fin_cases b <;>
      simp [genericSixOutputCorankTwoMinors,sixOutputCorankTwoMinors,
        sixOutputAlternatingMatrix,hp,H]
  have h := plucker_relation_coefficient_derivation D
    (genericSixOutputCorankTwoMinors (K:=K) q)
    (generic_six_output_corank_two_minors_plucker q hq)
    (sixOutputQuad i 0) (sixOutputQuad i 1) (sixOutputQuad i 2) (sixOutputQuad i 3)
  rw [he] at h
  have hH : (fun j => H (sixOutputPair j).1 (sixOutputPair j).2)=
      genericSixOutputCorankTwoGradients (K:=K) q t := by
    funext j
    exact sixOutputAlternatingMatrix_upper _ j
  rw [← sixOutputPluckerTangent_mulVec, hH] at h
  exact h

end FD56
