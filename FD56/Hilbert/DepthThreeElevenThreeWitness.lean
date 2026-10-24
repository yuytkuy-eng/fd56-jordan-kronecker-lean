/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthThreeElevenThreeData
import FD56.Hilbert.DepthThreeBetaSingleTest

/-! A vanishing auxiliary-kernel certificate for eleven states and three rows. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K : Type*} [Field K]
set_option maxHeartbeats 4000000

noncomputable def elevenThreeM0 : Matrix (Fin 11) (Fin 11) K :=
  ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

noncomputable def elevenThreeP0 : Matrix (Fin 3) (Fin 11) K :=
  ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

theorem elevenThree_evalM : (elevenThreeM (K := K)).map (Polynomial.evalRingHom 0) = elevenThreeM0 := by
  ext i j
  fin_cases i <;> (fin_cases j <;> norm_num [elevenThreeM,elevenThreeM0])

theorem elevenThree_evalP : (elevenThreeP (K := K)).map (Polynomial.evalRingHom 0) = elevenThreeP0 := by
  ext i j
  fin_cases i <;> (fin_cases j <;> norm_num [elevenThreeP,elevenThreeP0])

theorem elevenThree_M0_action (v : Fin 11 → K) :
    elevenThreeM0 *ᵥ v = ![v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, 0, 0] := by
  funext i
  fin_cases i <;> simp [elevenThreeM0,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

theorem elevenThree_P0_action (v : Fin 11 → K) :
    elevenThreeP0 *ᵥ v = ![v 0, v 5 + v 8, v 1] := by
  funext i
  fin_cases i <;> simp [elevenThreeP0,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

theorem elevenThree_constant_surjective :
    Function.Surjective ((observabilityMatrix (elevenThreeM (K := K)) elevenThreeP 3).map
      (Polynomial.evalRingHom 0)).mulVec := by
  rw [observabilityMatrix_map,elevenThree_evalM,elevenThree_evalP]
  intro y
  let v : Fin 11 → K := ![y (0,0), y (0,2), y (1,0), y (1,2), y (2,0), y (2,2), 0, y (1,1), y (0,1) + -y (2,2), y (2,1), 0]
  refine ⟨v,?_⟩
  funext i
  rcases i with ⟨i,a⟩
  change ((elevenThreeP0 * elevenThreeM0^i.val) *ᵥ v) a = y (i,a)
  fin_cases i <;> (fin_cases a <;>
    simp [pow_succ,← Matrix.mulVec_mulVec,elevenThree_M0_action,elevenThree_P0_action,v])

theorem elevenThree_stack_injective :
    Function.Injective (observabilityMatrix (elevenThreeM (K := K)) elevenThreeP 3).transpose.mulVec := by
  apply polynomial_matrix_injective_of_zero
  rw [Matrix.transpose_map]
  exact matrix_transpose_injective_of_surjective _ elevenThree_constant_surjective

theorem elevenThree_stack_vectorA :
    observabilityMatrix (elevenThreeM (K := K)) elevenThreeP 3 *ᵥ elevenThreeVA0 = 0 := by
  funext i
  rcases i with ⟨i,a⟩
  change ((elevenThreeP * elevenThreeM^i.val) *ᵥ elevenThreeVA0) a = 0
  fin_cases i
  · simpa only [Fin.val_zero,pow_zero,Matrix.mul_one] using congrFun (elevenThree_outputA0 (K := K)) a
  · simpa only [Fin.val_one,pow_one,← Matrix.mulVec_mulVec,elevenThree_stepA0] using
      congrFun (elevenThree_outputA1 (K := K)) a
  · simpa only [Fin.val_two,pow_two,← Matrix.mulVec_mulVec,elevenThree_stepA0,elevenThree_stepA1] using
      congrFun (elevenThree_outputA2 (K := K)) a

theorem elevenThree_terminal_vectorA :
    (elevenThreeP (K := K)*elevenThreeM^3) *ᵥ elevenThreeVA0 = elevenThreeF := by
  simpa only [pow_succ,pow_zero,Matrix.one_mul,← Matrix.mulVec_mulVec,
    elevenThree_stepA0,elevenThree_stepA1,elevenThree_stepA2] using (elevenThree_outputA3 (K := K))

theorem elevenThree_stack_vectorB :
    observabilityMatrix (elevenThreeM (K := K)) elevenThreeP 3 *ᵥ elevenThreeVB0 = 0 := by
  funext i
  rcases i with ⟨i,a⟩
  change ((elevenThreeP * elevenThreeM^i.val) *ᵥ elevenThreeVB0) a = 0
  fin_cases i
  · simpa only [Fin.val_zero,pow_zero,Matrix.mul_one] using congrFun (elevenThree_outputB0 (K := K)) a
  · simpa only [Fin.val_one,pow_one,← Matrix.mulVec_mulVec,elevenThree_stepB0] using
      congrFun (elevenThree_outputB1 (K := K)) a
  · simpa only [Fin.val_two,pow_two,← Matrix.mulVec_mulVec,elevenThree_stepB0,elevenThree_stepB1] using
      congrFun (elevenThree_outputB2 (K := K)) a

theorem elevenThree_terminal_vectorB :
    (elevenThreeP (K := K)*elevenThreeM^3) *ᵥ elevenThreeVB0 = elevenThreeG := by
  simpa only [pow_succ,pow_zero,Matrix.one_mul,← Matrix.mulVec_mulVec,
    elevenThree_stepB0,elevenThree_stepB1,elevenThree_stepB2] using (elevenThree_outputB3 (K := K))

private theorem elevenThree_bezout_factor (u v p q r : K[X]) :
    u*r*p+v*r*q=(u*p+v*q)*r := by ring

private theorem elevenThree_cross_relations (a b c f0 f1 f2 g0 g1 g2 : K[X])
    (hf : a*f0+b*f1+c*f2=0) (hg : a*g0+b*g1+c*g2=0) :
    a*(f2*g0-f0*g2)-b*(f1*g2-f2*g1)=0 ∧
      a*(f0*g1-f1*g0)-c*(f1*g2-f2*g1)=0 := by
  constructor
  · linear_combination f2*hg-g2*hf
  · linear_combination g1*hf-f1*hg

variable [CharZero K]

theorem elevenThree_coprime : IsCoprime (elevenThreeT0 (K := K)) elevenThreeT1 := by
  let c : K := 322424898635926472014997778402824608
  have hc : c ≠ 0 := by norm_num [c]
  refine ⟨elevenThreeU*C c⁻¹,elevenThreeW*C c⁻¹,?_⟩
  calc
    _ = (elevenThreeU*elevenThreeT0 + elevenThreeW*elevenThreeT1)*C c⁻¹ :=
      elevenThree_bezout_factor _ _ _ _ _
    _ = 1 := by
      rw [elevenThree_bezout]
      change C c * C c⁻¹ = 1
      rw [← C_mul,mul_inv_cancel₀ hc,C_1]

theorem elevenThree_T0_degree_lower : 26 ≤ (elevenThreeT0 (K := K)).natDegree := by
  apply Polynomial.le_natDegree_of_ne_zero
  norm_num [elevenThreeT0,integerPolynomial_coeff,List.getD]

theorem elevenThree_short_relations (a b c : K[X]) (ha : a.natDegree ≤ 25)
    (hf : a*elevenThreeF 0+b*elevenThreeF 1+c*elevenThreeF 2=0)
    (hg : a*elevenThreeG 0+b*elevenThreeG 1+c*elevenThreeG 2=0) :
    a=0 ∧ b=0 ∧ c=0 := by
  obtain ⟨h01,h02⟩ := elevenThree_cross_relations a b c
    (elevenThreeF 0) (elevenThreeF 1) (elevenThreeF 2)
    (elevenThreeG 0) (elevenThreeG 1) (elevenThreeG 2) hf hg
  rw [← elevenThree_cross1,← elevenThree_cross0] at h01
  rw [← elevenThree_cross2,← elevenThree_cross0] at h02
  have hd : elevenThreeT0 ∣ a := elevenThree_coprime.dvd_of_dvd_mul_right
    (show elevenThreeT0 ∣ a*elevenThreeT1 from ⟨b,(sub_eq_zero.mp h01).trans (mul_comm b _)⟩)
  have hz : a=0 := by
    by_contra hn
    have hh := Polynomial.natDegree_le_of_dvd hd hn
    have hl := elevenThree_T0_degree_lower (K := K)
    omega
  have hT : elevenThreeT0 (K := K) ≠ 0 := by
    intro ht
    have hh := elevenThree_T0_degree_lower (K := K)
    rw [ht,Polynomial.natDegree_zero] at hh
    omega
  rw [hz,zero_mul,zero_sub,neg_eq_zero] at h01 h02
  exact ⟨hz,(mul_eq_zero.mp h01).resolve_right hT,(mul_eq_zero.mp h02).resolve_right hT⟩

theorem elevenThree_beta_kernel_zero :
    Module.finrank K (boundedObservabilityBetaKernel 3
      (elevenThreeM (K := K)) elevenThreeP 25)=0 := by
  have hbot : boundedObservabilityBetaKernel 3 (elevenThreeM (K := K)) elevenThreeP 25 = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro z hz
    let w : boundedObservabilityBetaKernel 3 (elevenThreeM (K := K)) elevenThreeP 25 := ⟨z,hz⟩
    have hr := boundedObservabilityBetaKernel_relation 3 elevenThreeM elevenThreeP 25 w
    have hF := congrArg (fun v : Fin 11 → K[X] => dotProduct elevenThreeVA0 v) hr
    have hG := congrArg (fun v : Fin 11 → K[X] => dotProduct elevenThreeVB0 v) hr
    dsimp only at hF hG
    rw [dotProduct_mulVec,Matrix.vecMul_transpose,elevenThree_terminal_vectorA,
      dotProduct_mulVec,Matrix.vecMul_transpose,elevenThree_stack_vectorA] at hF
    rw [dotProduct_mulVec,Matrix.vecMul_transpose,elevenThree_terminal_vectorB,
      dotProduct_mulVec,Matrix.vecMul_transpose,elevenThree_stack_vectorB] at hG
    have hf : (z.1 0).val*elevenThreeF 0+(z.1 1).val*elevenThreeF 1+(z.1 2).val*elevenThreeF 2=0 := by
      simpa [w,dotProduct,Fin.sum_univ_succ,mul_comm,add_assoc] using hF
    have hg : (z.1 0).val*elevenThreeG 0+(z.1 1).val*elevenThreeG 1+(z.1 2).val*elevenThreeG 2=0 := by
      simpa [w,dotProduct,Fin.sum_univ_succ,mul_comm,add_assoc] using hG
    obtain ⟨h0,h1,h2⟩ := elevenThree_short_relations _ _ _ (boundedPoly_degree 25 (z.1 0)) hf hg
    have ht : (fun i => (z.1 i).val)=0 := by
      funext i
      fin_cases i
      · exact h0
      · exact h1
      · exact h2
    have hd : (fun i => (z.2 i).val)=0 := by
      apply elevenThree_stack_injective (K := K)
      change _ = (observabilityMatrix (elevenThreeM (K := K)) elevenThreeP 3).transpose *ᵥ 0
      rw [Matrix.mulVec_zero]
      change (observabilityMatrix (elevenThreeM (K := K)) elevenThreeP 3).transpose *ᵥ
        (fun i => (z.2 i).val)=0
      change (elevenThreeP*elevenThreeM^3).transpose *ᵥ (fun i => (z.1 i).val)=_ at hr
      rw [ht,Matrix.mulVec_zero] at hr
      exact hr.symm
    apply Prod.ext
    · funext i
      apply Subtype.ext
      exact congrFun ht i
    · funext i
      apply Subtype.ext
      exact congrFun hd i
  rw [hbot,finrank_bot]

end FD56
