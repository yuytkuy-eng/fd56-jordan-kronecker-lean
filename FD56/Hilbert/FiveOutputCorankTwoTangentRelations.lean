/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericFiveOutputCorankTwoSpecialization

/-! The five Plucker tangent equations annihilate the actual signed
observability gradients in the five-output corank-two range. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxHeartbeats 2000000

variable {K : Type*} [Field K] [CharZero K]

theorem generic_five_output_corank_two_minors_plucker (q : ℕ) (hq : 0<q)
    (i j k l : Fin 5) :
    pluckerQuadraticRelation (genericFiveOutputCorankTwoMinors (K:=K) q) i j k l=0 := by
  obtain ⟨a,b,u,v,_,_,_,_,hF,_⟩ :=
    generic_five_output_corank_two_full_specialization_faithful (K:=K) q hq
  rw [hF]
  simpa only [one_smul] using scaled_wedge_plucker_relation
    (1 : (AffineCoefficientField K (MatrixParameters (Fin (5*q+3)) (Fin 5)))[X]) u v i j k l

theorem generic_five_output_corank_two_gradient_tangent (q : ℕ) (hq : 0<q) :
    fiveOutputPluckerTangent (genericFiveOutputCorankTwoMinors (K:=K) q) *
      (genericFiveOutputCorankTwoGradients (K:=K) q).transpose=0 := by
  funext i t
  obtain ⟨D,hD⟩ := generic_five_output_corank_two_gradient_derivation (K:=K) q t
  have hp (j : Fin 10) : polynomialCoefficientDerivation D
      (fiveOutputCorankTwoMinor q (genericAffineSquare K _ _) (genericAffineRows K _ _) j)=
        genericFiveOutputCorankTwoGradients (K:=K) q t j := by
    simpa only [genericFiveOutputCorankTwoMinors,fiveOutputCorankTwoMinors,
      fiveOutputAlternatingMatrix_upper] using hD j
  let H := fiveOutputAlternatingMatrix (genericFiveOutputCorankTwoGradients (K:=K) q t)
  have he : (fun a b => polynomialCoefficientDerivation D
      (genericFiveOutputCorankTwoMinors (K:=K) q a b))=H := by
    funext a b
    fin_cases a <;> fin_cases b <;>
      simp [genericFiveOutputCorankTwoMinors,fiveOutputCorankTwoMinors,
        fiveOutputAlternatingMatrix,hp,H]
  have h := plucker_relation_coefficient_derivation D
    (genericFiveOutputCorankTwoMinors (K:=K) q)
    (generic_five_output_corank_two_minors_plucker q hq)
    (fiveOutputQuad i 0) (fiveOutputQuad i 1) (fiveOutputQuad i 2) (fiveOutputQuad i 3)
  rw [he] at h
  have hH : (fun j => H (fiveOutputPair j).1 (fiveOutputPair j).2)=
      genericFiveOutputCorankTwoGradients (K:=K) q t := by
    funext j
    exact fiveOutputAlternatingMatrix_upper _ j
  rw [← fiveOutputPluckerTangent_mulVec, hH] at h
  exact h

end FD56
