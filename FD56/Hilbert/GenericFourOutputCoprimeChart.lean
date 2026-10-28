/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericInteriorDegreeBalance
import FD56.Hilbert.FourOutputCoprimeChart
import FD56.Hilbert.FourOutputMinorDegrees
import FD56.LinearAlgebra.PluckerConstantOutputDerivation

/-! The actual generic four-output minors enter a full-degree coprime chart
through an invertible output change defined over the base field. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option Elab.async false
set_option maxHeartbeats 2000000

variable {K : Type*} [Field K]

private theorem generic_four_output_equal_degree_basis (q : ℕ) (hq : 0<q) :
    ∃ B : Basis (Fin 2)
      (AffineCoefficientField K (MatrixParameters (Fin (4*q+2)) (Fin 4)))[X]
      (LinearMap.ker (Matrix.toLin' (observabilityMatrix
        (genericAffineSquare K (Fin (4*q+2)) (Fin 4))
        (genericAffineRows K (Fin (4*q+2)) (Fin 4)) q))),
      (∀ i j, (polynomialKernelBasisMatrix _ B i j).natDegree≤q*(q+1)) ∧
      Function.Injective (Matrix.mulVec
        (fun i j => (polynomialKernelBasisMatrix _ B i j).coeff (q*(q+1)))) := by
  let M := genericAffineSquare K (Fin (4*q+2)) (Fin 4)
  let P := genericAffineRows K (Fin (4*q+2)) (Fin 4)
  let O := observabilityMatrix M P q
  have hlo : q*Fintype.card (Fin 4)<Fintype.card (Fin (4*q+2)) := by
    simp only [Fintype.card_fin]; omega
  have hhi : Fintype.card (Fin (4*q+2))<(q+1)*Fintype.card (Fin 4) := by
    simp only [Fintype.card_fin]; omega
  obtain ⟨k,Bv,a,hV,hVL,_,_⟩ := polynomial_kernel_has_minimal_basis O
  have hAlpha : HasMinimalKernelDegrees O (List.ofFn a) :=
    ⟨k,Bv,a,hV,hVL,List.Perm.refl _⟩
  obtain ⟨hk,ha⟩ := generic_observability_kernel_degree_budget (K:=K)
    q hlo (List.ofFn a) hAlpha
  simp only [List.length_ofFn,List.sum_ofFn,Fintype.card_fin] at hk ha
  have hk2 : k=2 := by omega
  subst k
  let G := P*M^q*polynomialKernelBasisMatrix O Bv
  obtain ⟨l,Bt,b,hT,hTL,_,_⟩ := polynomial_kernel_has_minimal_basis G.transpose
  have hBeta : HasMinimalKernelDegrees G.transpose (List.ofFn b) :=
    ⟨l,Bt,b,hT,hTL,List.Perm.refl _⟩
  obtain ⟨hl,_⟩ := generic_terminal_kernel_degree_budget (K:=K) q
    (by simp) hlo hhi Bv a hV hVL (List.ofFn b) hBeta
  simp only [List.length_ofFn,Fintype.card_fin] at hl
  have hl2 : l=2 := by omega
  subst l
  obtain ⟨hba,_⟩ := generic_interior_auxiliary_degrees_balanced (K:=K)
    2 2 q hq Bv Bt a b hV hT hVL hTL
  have hsum : a 0+a 1=2*(q*(q+1)) := by
    simp only [Fin.sum_univ_two] at ha
    nlinarith
  have h01 := hba 0 1
  have h10 := hba 1 0
  have heq0 : a 0=q*(q+1) := by omega
  have heq1 : a 1=q*(q+1) := by omega
  have heq : ∀ i, a i=q*(q+1) := by
    intro i
    fin_cases i
    · exact heq0
    · exact heq1
  refine ⟨Bv,?_,?_⟩
  · simpa only [heq] using hV
  · simpa only [heq] using hVL

theorem generic_four_output_coprime_chart [Infinite K] (q : ℕ) (hq : 0<q) :
    ∃ Q S : Matrix (Fin 4) (Fin 4) K,
      Q*S=1 ∧ S*Q=1 ∧
      let F := pluckerConstantOutputChange Q
        (genericFourOutputInteriorMinors (K:=K) q)
      (∀ i, (F i).natDegree≤2*(q+1)^2) ∧
      (F 0).natDegree=2*(q+1)^2 ∧
      IsCoprime (F 0) (F 1) ∧
      pluckerQuadric F=0 ∧
      4*(2*(q+1)^2)+5 ≤
        Module.finrank
          (AffineCoefficientField K (MatrixParameters (Fin (4*q+2)) (Fin 4)))
          (LinearMap.range (polynomialDerivationImageMap (K:=K) F)) := by
  classical
  let L := AffineCoefficientField K (MatrixParameters (Fin (4*q+2)) (Fin 4))
  let M := genericAffineSquare K (Fin (4*q+2)) (Fin 4)
  let P := genericAffineRows K (Fin (4*q+2)) (Fin 4)
  let O := observabilityMatrix M P q
  have hlo : q*Fintype.card (Fin 4)<Fintype.card (Fin (4*q+2)) := by
    simp only [Fintype.card_fin]; omega
  have hhi : Fintype.card (Fin (4*q+2))<(q+1)*Fintype.card (Fin 4) := by
    simp only [Fintype.card_fin]; omega
  obtain ⟨B,hV,hVL⟩ := generic_four_output_equal_degree_basis (K:=K) q hq
  let G := P*M^q*polynomialKernelBasisMatrix O B
  obtain ⟨R,hR⟩ := generic_terminal_kernel_left_inverse (K:=K) q (by simp) hlo hhi B
  obtain ⟨hG,hGL⟩ := generic_terminal_kernel_degree_and_leading (K:=K)
    q hhi.le B (fun _ => q*(q+1)) hV hVL
  have hdeg : q*(q+1)+q+1=(q+1)^2 := by ring
  simp only [hdeg] at hG hGL
  obtain ⟨Q,S,hQS,hSQ,hd,hcop⟩ := exists_four_output_coprime_chart_action
    (K:=K) G R hR ((q+1)^2) hG hGL
  obtain ⟨U,hU⟩ := generic_affine_wide_observability_right_inverse (K:=K) q hlo
  obtain ⟨c,hc,hcF⟩ := fourOutputInteriorMinors_common_scalar q M P U hU B
  let F := genericFourOutputInteriorMinors (K:=K) q
  let H := fourOutputPluckerVector G
  have hF : F=c • H := by
    funext i
    simpa only [F,H,G,O,M,P,Pi.smul_apply,Polynomial.smul_eq_C_mul] using hcF i
  have hchange : pluckerConstantOutputChange Q F=c • pluckerConstantOutputChange Q H := by
    rw [hF,map_smul]
  have hu : IsUnit (C c : L[X]) := Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc)
  refine ⟨Q,S,hQS,hSQ,?_,?_,?_,?_,?_⟩
  · exact pluckerConstantOutputChange_degree_bound Q F _
      (generic_four_output_minors_degree q)
  · change (pluckerConstantOutputChange Q F 0).natDegree=2*(q+1)^2
    rw [hchange,Pi.smul_apply,Polynomial.smul_eq_C_mul,Polynomial.natDegree_C_mul hc]
    exact hd
  · change IsCoprime (pluckerConstantOutputChange Q F 0) (pluckerConstantOutputChange Q F 1)
    rw [hchange]
    simpa only [Pi.smul_apply,Polynomial.smul_eq_C_mul] using
      (isCoprime_mul_unit_left hu _ _).mpr hcop
  · change pluckerQuadric (pluckerConstantOutputChange Q F)=0
    rw [pluckerConstantOutputChange_quadric]
    have hz : pluckerQuadric F=0 := generic_four_output_minors_relation q
    rw [hz,mul_zero]
  · change 4*(2*(q+1)^2)+5≤Module.finrank L
      (LinearMap.range (polynomialDerivationImageMap (K:=K) (pluckerConstantOutputChange Q F)))
    rw [pluckerConstantOutputChange_derivation_rank Q S hQS hSQ]
    exact generic_four_output_minors_derivation_rank_lower q hq

end FD56
