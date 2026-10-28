/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthFourThirteenThreeSyzygyData
import FD56.Hilbert.ObservabilityBetaVectorBound

/-! Exact short-relation bounds for thirteen states and three rows at depth four. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K : Type*} [Field K]
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 200000
set_option Elab.async false

def thirteenThreeQ4M0 : Matrix (Fin 13) (Fin 13) K :=
  (thirteenThreeQ4M (K := K)).map (Polynomial.evalRingHom 0)

def thirteenThreeQ4P0 : Matrix (Fin 3) (Fin 13) K :=
  (thirteenThreeQ4P (K := K)).map (Polynomial.evalRingHom 0)

def thirteenThreeQ4Selector (i : Fin 4) (a : Fin 3) : Fin 13 :=
  ⟨3*i.val+a.val,by omega⟩

def thirteenThreeQ4Row (i : Fin 4 × Fin 3) : Fin 13 := thirteenThreeQ4Selector i.1 i.2

def thirteenThreeQ4ConstantBlock (i : Fin 4) : Matrix (Fin 3) (Fin 13) K :=
  (1 : Matrix (Fin 13) (Fin 13) K).submatrix (thirteenThreeQ4Selector i) id

def thirteenThreeQ4R0 : Matrix (Fin 13) (Fin 4 × Fin 3) K :=
  (1 : Matrix (Fin 13) (Fin 13) K).submatrix id thirteenThreeQ4Row

theorem thirteenThreeQ4_P0_eq :
    thirteenThreeQ4P0 (K := K) = thirteenThreeQ4ConstantBlock 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [thirteenThreeQ4P0,thirteenThreeQ4P,thirteenThreeQ4ConstantBlock,
      thirteenThreeQ4Selector,Matrix.submatrix_apply,Matrix.one_apply]

theorem thirteenThreeQ4_constant_step (i : Fin 3) :
    thirteenThreeQ4ConstantBlock (K := K) i.castSucc * thirteenThreeQ4M0 (K := K) =
      thirteenThreeQ4ConstantBlock i.succ := by
  calc
    _ = (thirteenThreeQ4M0 (K := K)).submatrix (thirteenThreeQ4Selector i.castSucc) id := by
      simpa only [thirteenThreeQ4ConstantBlock,Equiv.refl_apply,Function.id_comp] using
        Matrix.one_submatrix_mul (thirteenThreeQ4Selector i.castSucc)
          (Equiv.refl (Fin 13)) (thirteenThreeQ4M0 (K := K))
    _ = _ := by
      ext a j
      fin_cases i <;> fin_cases a <;> fin_cases j <;>
        norm_num [thirteenThreeQ4M0,thirteenThreeQ4M,thirteenThreeQ4ConstantBlock,
          thirteenThreeQ4Selector,Matrix.submatrix_apply,Matrix.one_apply]

theorem thirteenThreeQ4_evalO :
    (observabilityMatrix (thirteenThreeQ4M (K := K)) thirteenThreeQ4P 4).map
      (Polynomial.evalRingHom 0) =
      (1 : Matrix (Fin 13) (Fin 13) K).submatrix thirteenThreeQ4Row id := by
  have h0 := thirteenThreeQ4_constant_step (K := K) 0
  have h1 := thirteenThreeQ4_constant_step (K := K) 1
  have h2 := thirteenThreeQ4_constant_step (K := K) 2
  change thirteenThreeQ4ConstantBlock (K := K) 0 * thirteenThreeQ4M0 = thirteenThreeQ4ConstantBlock 1 at h0
  change thirteenThreeQ4ConstantBlock (K := K) 1 * thirteenThreeQ4M0 = thirteenThreeQ4ConstantBlock 2 at h1
  change thirteenThreeQ4ConstantBlock (K := K) 2 * thirteenThreeQ4M0 = thirteenThreeQ4ConstantBlock 3 at h2
  rw [observabilityMatrix_map]
  change observabilityMatrix (thirteenThreeQ4M0 (K := K)) thirteenThreeQ4P0 4 = _
  rw [thirteenThreeQ4_P0_eq]
  funext i j
  rcases i with ⟨i,a⟩
  change ((show Matrix (Fin 3) (Fin 13) K from
      thirteenThreeQ4ConstantBlock (K := K) 0 * (thirteenThreeQ4M0 (K := K))^i.val) a j) =
    thirteenThreeQ4ConstantBlock (K := K) i a j
  fin_cases i
  · simp only [Fin.val_zero,pow_zero,Matrix.mul_one] <;> rfl
  · simpa only [Fin.val_one,pow_one] using congrFun (congrFun h0 a) j
  · simp only [Fin.val_two,pow_two,← Matrix.mul_assoc]
    rw [h0,h1] <;> rfl
  · simp only [Fin.reduceFinMk,pow_succ,pow_zero,Matrix.mul_one,← Matrix.mul_assoc]
    rw [h0,h1,h2]

theorem thirteenThreeQ4_constant_right_inverse :
    (observabilityMatrix (thirteenThreeQ4M (K := K)) thirteenThreeQ4P 4).map
      (Polynomial.evalRingHom 0) * thirteenThreeQ4R0 (K := K) = 1 := by
  rw [thirteenThreeQ4_evalO]
  have hr : Function.Injective thirteenThreeQ4Row := by decide
  calc
    _ = (thirteenThreeQ4R0 (K := K)).submatrix thirteenThreeQ4Row id := by
      simpa only [Equiv.refl_apply,Function.id_comp] using
        Matrix.one_submatrix_mul thirteenThreeQ4Row (Equiv.refl (Fin 13)) (thirteenThreeQ4R0 (K := K))
    _ = 1 := by
      ext i j
      simp [thirteenThreeQ4R0,Matrix.submatrix_apply,Matrix.one_apply,hr.eq_iff]

theorem thirteenThreeQ4_stack_injective :
    Function.Injective (observabilityMatrix (thirteenThreeQ4M (K := K)) thirteenThreeQ4P 4).transpose.mulVec := by
  apply polynomial_matrix_injective_of_zero
  rw [Matrix.transpose_map]
  apply matrix_transpose_injective_of_surjective
  intro v
  refine ⟨thirteenThreeQ4R0 *ᵥ v,?_⟩
  rw [Matrix.mulVec_mulVec,thirteenThreeQ4_constant_right_inverse,Matrix.one_mulVec]

theorem thirteenThreeQ4_stack_vector :
    observabilityMatrix (thirteenThreeQ4M (K := K)) thirteenThreeQ4P 4 *ᵥ thirteenThreeQ4V0 = 0 := by
  funext i
  rcases i with ⟨i,a⟩
  change ((thirteenThreeQ4P * thirteenThreeQ4M^i.val) *ᵥ thirteenThreeQ4V0) a = 0
  fin_cases i
  · simpa only [Fin.val_zero,pow_zero,Matrix.mul_one] using congrFun (thirteenThreeQ4_output0 (K := K)) a
  · simpa only [Fin.val_one,pow_one,← Matrix.mulVec_mulVec,thirteenThreeQ4_step0] using
      congrFun (thirteenThreeQ4_output1 (K := K)) a
  · simpa only [Fin.val_two,pow_two,← Matrix.mulVec_mulVec,thirteenThreeQ4_step0,thirteenThreeQ4_step1] using
      congrFun (thirteenThreeQ4_output2 (K := K)) a
  · simpa only [Fin.reduceFinMk,pow_succ,pow_zero,Matrix.one_mul,← Matrix.mulVec_mulVec,
      thirteenThreeQ4_step0,thirteenThreeQ4_step1,thirteenThreeQ4_step2] using
      congrFun (thirteenThreeQ4_output3 (K := K)) a

theorem thirteenThreeQ4_terminal_vector :
    (thirteenThreeQ4P (K := K)*thirteenThreeQ4M^4) *ᵥ thirteenThreeQ4V0 = thirteenThreeQ4F := by
  simpa only [pow_succ,pow_zero,Matrix.one_mul,← Matrix.mulVec_mulVec,
    thirteenThreeQ4_step0,thirteenThreeQ4_step1,thirteenThreeQ4_step2,thirteenThreeQ4_step3] using
    (thirteenThreeQ4_output4 (K := K))

variable [CharZero K]

theorem thirteenThreeQ4_beta_kernel_bound (d : ℕ) :
    Module.finrank K (boundedObservabilityBetaKernel 4
      (thirteenThreeQ4M (K := K)) thirteenThreeQ4P d) ≤
      ∑ j : Fin 2, (d+1-thirteenThreeQ4SyzygyDegrees j) := by
  exact observability_beta_finrank_le_scaled_cofactors 4 thirteenThreeQ4M thirteenThreeQ4P
    thirteenThreeQ4V0 thirteenThreeQ4F thirteenThreeQ4_terminal_vector thirteenThreeQ4_stack_vector
    thirteenThreeQ4_stack_injective thirteenThreeQ4Syzygy thirteenThreeQ4Bezout
    18924188987186115287972366182496508804060115214692810625279438204130 12773389666956212971886698992960980043752846546706889737002263707097708032 (by norm_num) (by norm_num)
    thirteenThreeQ4_syzygy_cofactors thirteenThreeQ4_syzygy_bezout
    thirteenThreeQ4SyzygyDegrees thirteenThreeQ4_syzygy_degree thirteenThreeQ4_syzygy_leading_injective d

theorem thirteenThreeQ4_beta_kernel_zero :
    Module.finrank K (boundedObservabilityBetaKernel 4
      (thirteenThreeQ4M (K := K)) thirteenThreeQ4P 16)=0 := by
  apply Nat.eq_zero_of_le_zero
  simpa [thirteenThreeQ4SyzygyDegrees,Fin.sum_univ_succ] using (thirteenThreeQ4_beta_kernel_bound (K := K) 16)

theorem thirteenThreeQ4_beta_kernel_seventeen_le :
    Module.finrank K (boundedObservabilityBetaKernel 4
      (thirteenThreeQ4M (K := K)) thirteenThreeQ4P 17)≤1 := by
  simpa [thirteenThreeQ4SyzygyDegrees,Fin.sum_univ_succ] using (thirteenThreeQ4_beta_kernel_bound (K := K) 17)

end FD56
