/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthThreeSevenTwoData

/-! A bounded auxiliary-kernel certificate in characteristic zero. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K : Type*} [Field K]

def sevenTwoM0 : Matrix (Fin 7) (Fin 7) K :=
  ![![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0]]

def sevenTwoP0 : Matrix (Fin 2) (Fin 7) K :=
  ![![0, 0, 0, 0, 0, 0, 1], ![1, 0, 0, 1, 0, 0, 0]]

theorem sevenTwo_evalM : (sevenTwoM (K := K)).map (Polynomial.evalRingHom 0) = sevenTwoM0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [sevenTwoM,sevenTwoM0]

theorem sevenTwo_evalP : (sevenTwoP (K := K)).map (Polynomial.evalRingHom 0) = sevenTwoP0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [sevenTwoP,sevenTwoP0]

def sevenTwoR0 : Matrix (Fin 7) (Fin 3 × Fin 2) K :=
  fun i j => ![![![0, 0], ![0, 0], ![1, 0]], ![![0, 0], ![0, 0], ![0, 1]], ![![0, 0], ![0, 1], ![0, 0]], ![![0, 1], ![0, 0], ![-1, 0]], ![![0, 0], ![0, 0], ![0, 0]], ![![0, 0], ![1, 0], ![0, 0]], ![![1, 0], ![0, 0], ![0, 0]]] i j.1 j.2

set_option maxHeartbeats 4000000 in
theorem sevenTwo_constant_right_inverse :
    (observabilityMatrix (sevenTwoM (K := K)) sevenTwoP 3).map
      (Polynomial.evalRingHom 0) * (sevenTwoR0 (K := K)) = 1 := by
  rw [observabilityMatrix_map,sevenTwo_evalM,sevenTwo_evalP]
  ext i j
  rcases i with ⟨i,a⟩
  rcases j with ⟨j,b⟩
  fin_cases i <;> fin_cases a <;> fin_cases j <;> fin_cases b <;>
    norm_num [observabilityMatrix,sevenTwoM0,sevenTwoP0,sevenTwoR0,
      Matrix.mul_apply,Fin.sum_univ_succ,pow_succ,Matrix.one_apply,Prod.ext_iff]

theorem sevenTwo_stack_injective :
    Function.Injective (observabilityMatrix (sevenTwoM (K := K)) sevenTwoP 3).transpose.mulVec := by
  apply polynomial_matrix_injective_of_zero
  rw [Matrix.transpose_map]
  apply matrix_transpose_injective_of_surjective
  intro v
  refine ⟨sevenTwoR0 *ᵥ v,?_⟩
  rw [Matrix.mulVec_mulVec,sevenTwo_constant_right_inverse,Matrix.one_mulVec]

theorem sevenTwo_stack_vector :
    observabilityMatrix (sevenTwoM (K := K)) sevenTwoP 3 *ᵥ sevenTwoV0 = 0 := by
  funext i
  rcases i with ⟨i,a⟩
  change ((sevenTwoP * sevenTwoM^i.val) *ᵥ sevenTwoV0) a = 0
  fin_cases i
  · simpa only [Fin.val_zero,pow_zero,Matrix.mul_one] using congrFun (sevenTwo_output0 (K := K)) a
  · simpa only [Fin.val_one,pow_one,← Matrix.mulVec_mulVec,sevenTwo_step0] using
      congrFun (sevenTwo_output1 (K := K)) a
  · simpa only [Fin.val_two,pow_two,← Matrix.mulVec_mulVec,sevenTwo_step0,sevenTwo_step1] using
      congrFun (sevenTwo_output2 (K := K)) a

theorem sevenTwo_terminal_vector :
    (sevenTwoP (K := K)*sevenTwoM^3) *ᵥ sevenTwoV0 = ![sevenTwoF0,sevenTwoF1] := by
  simpa only [pow_succ,pow_zero,Matrix.one_mul,← Matrix.mulVec_mulVec,
    sevenTwo_step0,sevenTwo_step1,sevenTwo_step2] using (sevenTwo_output3 (K := K))

variable [CharZero K]

theorem sevenTwo_coprime : IsCoprime (sevenTwoF0 (K := K)) sevenTwoF1 := by
  let c : K := 49592742382823085437211
  have hc : c ≠ 0 := by norm_num [c]
  refine ⟨sevenTwoU*C c⁻¹,sevenTwoW*C c⁻¹,?_⟩
  calc
    _ = (sevenTwoU*sevenTwoF0 + sevenTwoW*sevenTwoF1)*C c⁻¹ := by ring
    _ = 1 := by
      rw [sevenTwo_bezout]
      change C c * C c⁻¹ = 1
      rw [← C_mul,mul_inv_cancel₀ hc,C_1]

theorem sevenTwo_F1_degree_lower : 16 ≤ (sevenTwoF1 (K := K)).natDegree := by
  apply Polynomial.le_natDegree_of_ne_zero
  norm_num [sevenTwoF1,Polynomial.coeff_add,Polynomial.coeff_neg,Polynomial.coeff_one]

theorem sevenTwo_short_relation (a b : K[X]) (ha : a.natDegree ≤ 15)
    (h : a*sevenTwoF0+b*sevenTwoF1=0) : a=0 ∧ b=0 := by
  have hdiv : sevenTwoF1 ∣ a := sevenTwo_coprime.symm.dvd_of_dvd_mul_right
    (show sevenTwoF1 ∣ a*sevenTwoF0 from ⟨-b,by linear_combination h⟩)
  have hz : a=0 := by
    by_contra hn
    have hh := Polynomial.natDegree_le_of_dvd hdiv hn
    have hl := sevenTwo_F1_degree_lower (K := K)
    omega
  have hF : sevenTwoF1 (K := K) ≠ 0 := by
    intro hf
    have hh := sevenTwo_F1_degree_lower (K := K)
    rw [hf,Polynomial.natDegree_zero] at hh
    omega
  refine ⟨hz,?_⟩
  rw [hz,zero_mul,zero_add] at h
  exact (mul_eq_zero.mp h).resolve_right hF

theorem sevenTwo_beta_kernel_zero :
    Module.finrank K (boundedObservabilityBetaKernel 3
      (sevenTwoM (K := K)) sevenTwoP 15)=0 := by
  have hbot : boundedObservabilityBetaKernel 3 (sevenTwoM (K := K)) sevenTwoP 15 = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro z hz
    let w : boundedObservabilityBetaKernel 3 (sevenTwoM (K := K)) sevenTwoP 15 := ⟨z,hz⟩
    have hr := boundedObservabilityBetaKernel_relation 3 sevenTwoM sevenTwoP 15 w
    have hh := congrArg (fun v : Fin 7 → K[X] => dotProduct sevenTwoV0 v) hr
    dsimp only at hh
    rw [dotProduct_mulVec,Matrix.vecMul_transpose,sevenTwo_terminal_vector,
      dotProduct_mulVec,Matrix.vecMul_transpose,sevenTwo_stack_vector] at hh
    have he : (z.1 0).val*sevenTwoF0+(z.1 1).val*sevenTwoF1=0 := by
      simpa [w,dotProduct,Fin.sum_univ_succ,mul_comm] using hh
    obtain ⟨h0,h1⟩ := sevenTwo_short_relation _ _ (boundedPoly_degree 15 (z.1 0)) he
    have ht : (fun i => (z.1 i).val)=0 := by
      funext i
      fin_cases i
      · exact h0
      · exact h1
    have hd : (fun i => (z.2 i).val)=0 := by
      apply sevenTwo_stack_injective (K := K)
      change _ = (observabilityMatrix (sevenTwoM (K := K)) sevenTwoP 3).transpose *ᵥ 0
      rw [Matrix.mulVec_zero]
      change (observabilityMatrix (sevenTwoM (K := K)) sevenTwoP 3).transpose *ᵥ
        (fun i => (z.2 i).val)=0
      change (sevenTwoP*sevenTwoM^3).transpose *ᵥ (fun i => (z.1 i).val)=_ at hr
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
