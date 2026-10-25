/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthThreeTenThreeSyzygyData
import FD56.LinearAlgebra.CofactorKernelComplement
import FD56.Hilbert.DepthThreeBetaSingleTest

/-! A bounded auxiliary-kernel certificate for ten states and three rows. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K : Type*} [Field K]
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

def tenThreeM0 : Matrix (Fin 10) (Fin 10) K :=
  ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

theorem tenThree_evalM : (tenThreeM (K := K)).map (Polynomial.evalRingHom 0) = tenThreeM0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [tenThreeM,tenThreeM0]

def tenThreeP0 : Matrix (Fin 3) (Fin 10) K :=
  ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 1, 0, 0, 0, 0, 0]]

theorem tenThree_evalP : (tenThreeP (K := K)).map (Polynomial.evalRingHom 0) = tenThreeP0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [tenThreeP,tenThreeP0]

def tenThreeR0 : Matrix (Fin 10) (Fin 3 × Fin 3) K :=
  fun i j => ![![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, -1, 0]], ![![0, 0, 0], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 1], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 1, 0]], ![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![-1, 0, 0], ![0, 0, 0], ![0, 0, 1]], ![![0, 0, 0], ![0, 0, 0], ![1, 0, 0]]] i j.1 j.2

theorem tenThree_constant_right_inverse :
    (observabilityMatrix (tenThreeM (K := K)) tenThreeP 3).map
      (Polynomial.evalRingHom 0) * (tenThreeR0 (K := K)) = 1 := by
  rw [observabilityMatrix_map,tenThree_evalM,tenThree_evalP]
  ext i j
  rcases i with ⟨i,a⟩
  rcases j with ⟨j,b⟩
  fin_cases i <;> fin_cases a <;> fin_cases j <;> fin_cases b <;>
    norm_num [observabilityMatrix,tenThreeM0,tenThreeP0,tenThreeR0,
      Matrix.mul_apply,Fin.sum_univ_succ,pow_succ,Matrix.one_apply,Prod.ext_iff]

theorem tenThree_stack_injective :
    Function.Injective (observabilityMatrix (tenThreeM (K := K)) tenThreeP 3).transpose.mulVec := by
  apply polynomial_matrix_injective_of_zero
  rw [Matrix.transpose_map]
  apply matrix_transpose_injective_of_surjective
  intro v
  refine ⟨tenThreeR0 *ᵥ v,?_⟩
  rw [Matrix.mulVec_mulVec,tenThree_constant_right_inverse,Matrix.one_mulVec]

theorem tenThree_stack_vector :
    observabilityMatrix (tenThreeM (K := K)) tenThreeP 3 *ᵥ tenThreeV0 = 0 := by
  funext i
  rcases i with ⟨i,a⟩
  change ((tenThreeP * tenThreeM^i.val) *ᵥ tenThreeV0) a = 0
  fin_cases i
  · simpa only [Fin.val_zero,pow_zero,Matrix.mul_one] using congrFun (tenThree_output0 (K := K)) a
  · simpa only [Fin.val_one,pow_one,← Matrix.mulVec_mulVec,tenThree_step0] using
      congrFun (tenThree_output1 (K := K)) a
  · simpa only [Fin.val_two,pow_two,← Matrix.mulVec_mulVec,tenThree_step0,tenThree_step1] using
      congrFun (tenThree_output2 (K := K)) a

theorem tenThree_terminal_vector :
    (tenThreeP (K := K)*tenThreeM^3) *ᵥ tenThreeV0 = tenThreeF := by
  simpa only [pow_succ,pow_zero,Matrix.one_mul,← Matrix.mulVec_mulVec,
    tenThree_step0,tenThree_step1,tenThree_step2] using (tenThree_output3 (K := K))

variable [CharZero K]

theorem tenThree_short_relation (E : Fin 3 → K[X])
    (hE : ∀ j, (E j).natDegree ≤ 10) (hrel : ∑ j, E j * tenThreeF j = 0) : E = 0 := by
  apply bounded_relation_eq_zero_of_scaled_cofactors tenThreeSyzygy tenThreeF tenThreeBezout
    (-279250) 40459886 (by norm_num) (by norm_num)
    tenThree_syzygy_cofactors tenThree_syzygy_bezout
    (fun _ => 11) 10 (by intro j; norm_num)
    tenThree_syzygy_degree tenThree_syzygy_leading_injective E hE
  simpa only [dotProduct,mul_comm] using hrel

theorem tenThree_beta_kernel_zero :
    Module.finrank K (boundedObservabilityBetaKernel 3
      (tenThreeM (K := K)) tenThreeP 10)=0 := by
  have hbot : boundedObservabilityBetaKernel 3 (tenThreeM (K := K)) tenThreeP 10 = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro z hz
    let w : boundedObservabilityBetaKernel 3 (tenThreeM (K := K)) tenThreeP 10 := ⟨z,hz⟩
    have hr := boundedObservabilityBetaKernel_relation 3 tenThreeM tenThreeP 10 w
    have hh := congrArg (fun v : Fin 10 → K[X] => dotProduct tenThreeV0 v) hr
    dsimp only at hh
    rw [dotProduct_mulVec,Matrix.vecMul_transpose,tenThree_terminal_vector,
      dotProduct_mulVec,Matrix.vecMul_transpose,tenThree_stack_vector] at hh
    have he : ∑ j, (z.1 j).val * tenThreeF j = 0 := by
      simpa [w,dotProduct,mul_comm] using hh
    have ht : (fun i => (z.1 i).val)=0 :=
      tenThree_short_relation _ (fun i => boundedPoly_degree 10 (z.1 i)) he
    have hd : (fun i => (z.2 i).val)=0 := by
      apply tenThree_stack_injective (K := K)
      change _ = (observabilityMatrix (tenThreeM (K := K)) tenThreeP 3).transpose *ᵥ 0
      rw [Matrix.mulVec_zero]
      change (observabilityMatrix (tenThreeM (K := K)) tenThreeP 3).transpose *ᵥ
        (fun i => (z.2 i).val)=0
      change (tenThreeP*tenThreeM^3).transpose *ᵥ (fun i => (z.1 i).val)=_ at hr
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
