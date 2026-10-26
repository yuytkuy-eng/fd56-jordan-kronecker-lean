/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthThreeThirteenFourSyzygyData
import FD56.Hilbert.ObservabilityBetaVectorBound

/-! Exact auxiliary-kernel bounds for thirteen states and four rows. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K : Type*} [Field K]
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 400000

def thirteenFourM0 : Matrix (Fin 13) (Fin 13) K :=
  (thirteenFourM (K := K)).map (Polynomial.evalRingHom 0)

theorem thirteenFour_evalM :
    (thirteenFourM (K := K)).map (Polynomial.evalRingHom 0) = thirteenFourM0 := rfl

def thirteenFourP0 : Matrix (Fin 4) (Fin 13) K :=
  (thirteenFourP (K := K)).map (Polynomial.evalRingHom 0)

theorem thirteenFour_evalP :
    (thirteenFourP (K := K)).map (Polynomial.evalRingHom 0) = thirteenFourP0 := rfl

def thirteenFourSelector : Fin 3 → Fin 4 → Fin 13 :=
  ![![⟨1,by decide⟩,⟨8,by decide⟩,⟨0,by decide⟩,⟨7,by decide⟩],
    ![⟨3,by decide⟩,⟨10,by decide⟩,⟨2,by decide⟩,⟨9,by decide⟩],
    ![⟨5,by decide⟩,⟨12,by decide⟩,⟨4,by decide⟩,⟨11,by decide⟩]]

def thirteenFourRow : Fin 3 × Fin 4 → Fin 13 := fun i => thirteenFourSelector i.1 i.2

def thirteenFourConstantBlock (i : Fin 3) : Matrix (Fin 4) (Fin 13) K :=
  (1 : Matrix (Fin 13) (Fin 13) K).submatrix (thirteenFourSelector i) id

def thirteenFourO0 : Matrix (Fin 3 × Fin 4) (Fin 13) K :=
  (1 : Matrix (Fin 13) (Fin 13) K).submatrix thirteenFourRow id

def thirteenFourR0 : Matrix (Fin 13) (Fin 3 × Fin 4) K :=
  (1 : Matrix (Fin 13) (Fin 13) K).submatrix id thirteenFourRow

theorem thirteenFour_P0_eq :
    thirteenFourP0 (K := K) = thirteenFourConstantBlock 0 := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals first
    | change (Polynomial.evalRingHom (0 : K)) (0 : K[X]) = 0
    | change (Polynomial.evalRingHom (0 : K)) (1 : K[X]) = 1
    | change (Polynomial.evalRingHom (0 : K)) (X : K[X]) = 0
  all_goals simp

theorem thirteenFour_constant_step (i : Fin 2) :
    thirteenFourConstantBlock (K := K) i.castSucc * thirteenFourM0 (K := K) =
      thirteenFourConstantBlock i.succ := by
  calc
    _ = (thirteenFourM0 (K := K)).submatrix (thirteenFourSelector i.castSucc) id := by
      simpa only [thirteenFourConstantBlock,Equiv.refl_apply,Function.id_comp] using
        Matrix.one_submatrix_mul (thirteenFourSelector i.castSucc)
          (Equiv.refl (Fin 13)) (thirteenFourM0 (K := K))
    _ = _ := by
      ext a j
      fin_cases i <;> fin_cases a <;> fin_cases j
      all_goals first
        | change (Polynomial.evalRingHom (0 : K)) (0 : K[X]) = 0
        | change (Polynomial.evalRingHom (0 : K)) (1 : K[X]) = 1
        | change (Polynomial.evalRingHom (0 : K)) (X : K[X]) = 0
      all_goals simp

theorem thirteenFour_evalO :
    (observabilityMatrix (thirteenFourM (K := K)) thirteenFourP 3).map
      (Polynomial.evalRingHom 0) = thirteenFourO0 := by
  have h0 := thirteenFour_constant_step (K := K) 0
  have h1 := thirteenFour_constant_step (K := K) 1
  change thirteenFourConstantBlock (K := K) 0 * thirteenFourM0 = thirteenFourConstantBlock 1 at h0
  change thirteenFourConstantBlock (K := K) 1 * thirteenFourM0 = thirteenFourConstantBlock 2 at h1
  rw [observabilityMatrix_map,thirteenFour_evalM,thirteenFour_evalP,thirteenFour_P0_eq]
  funext i j
  rcases i with ⟨i,a⟩
  change (thirteenFourConstantBlock (K := K) 0 * thirteenFourM0 (K := K)^i.val) a j =
    thirteenFourConstantBlock i a j
  fin_cases i
  · simp only [Fin.val_zero,pow_zero,Matrix.mul_one]
    rfl
  · simpa only [Fin.val_one,pow_one] using congrFun (congrFun h0 a) j
  · simp only [Fin.val_two,pow_two,← Matrix.mul_assoc]
    rw [h0,h1]
    rfl

theorem thirteenFour_constant_right_inverse :
    (observabilityMatrix (thirteenFourM (K := K)) thirteenFourP 3).map
      (Polynomial.evalRingHom 0) * (thirteenFourR0 (K := K)) = 1 := by
  rw [thirteenFour_evalO]
  have hr : Function.Injective thirteenFourRow := by decide
  calc
    _ = (thirteenFourR0 (K := K)).submatrix thirteenFourRow id := by
      simpa only [thirteenFourO0,Equiv.refl_apply,Function.id_comp] using
        Matrix.one_submatrix_mul thirteenFourRow (Equiv.refl (Fin 13)) (thirteenFourR0 (K := K))
    _ = 1 := by
      ext i j
      simp [thirteenFourR0,Matrix.submatrix_apply,Matrix.one_apply,hr.eq_iff]

theorem thirteenFour_stack_injective :
    Function.Injective (observabilityMatrix (thirteenFourM (K := K)) thirteenFourP 3).transpose.mulVec := by
  apply polynomial_matrix_injective_of_zero
  rw [Matrix.transpose_map]
  apply matrix_transpose_injective_of_surjective
  intro v
  refine ⟨thirteenFourR0 *ᵥ v,?_⟩
  rw [Matrix.mulVec_mulVec,thirteenFour_constant_right_inverse,Matrix.one_mulVec]

theorem thirteenFour_stack_vector :
    observabilityMatrix (thirteenFourM (K := K)) thirteenFourP 3 *ᵥ thirteenFourV0 = 0 := by
  funext i
  rcases i with ⟨i,a⟩
  change ((thirteenFourP * thirteenFourM^i.val) *ᵥ thirteenFourV0) a = 0
  fin_cases i
  · simpa only [Fin.val_zero,pow_zero,Matrix.mul_one] using congrFun (thirteenFour_output0 (K := K)) a
  · simpa only [Fin.val_one,pow_one,← Matrix.mulVec_mulVec,thirteenFour_step0] using
      congrFun (thirteenFour_output1 (K := K)) a
  · simpa only [Fin.val_two,pow_two,← Matrix.mulVec_mulVec,thirteenFour_step0,thirteenFour_step1] using
      congrFun (thirteenFour_output2 (K := K)) a

theorem thirteenFour_terminal_vector :
    (thirteenFourP (K := K)*thirteenFourM^3) *ᵥ thirteenFourV0 = thirteenFourF := by
  simpa only [pow_succ,pow_zero,Matrix.one_mul,← Matrix.mulVec_mulVec,
    thirteenFour_step0,thirteenFour_step1,thirteenFour_step2] using (thirteenFour_output3 (K := K))

variable [CharZero K]

theorem thirteenFour_beta_kernel_bound (d : ℕ) :
    Module.finrank K (boundedObservabilityBetaKernel 3
      (thirteenFourM (K := K)) thirteenFourP d) ≤
      ∑ j : Fin 3, (d + 1 - thirteenFourSyzygyDegrees j) := by
  exact observability_beta_finrank_le_scaled_cofactors 3 thirteenFourM thirteenFourP
    thirteenFourV0 thirteenFourF thirteenFour_terminal_vector thirteenFour_stack_vector
    thirteenFour_stack_injective thirteenFourSyzygy thirteenFourBezout
    7235563024 1241486621744 (by norm_num) (by norm_num)
    thirteenFour_syzygy_cofactors thirteenFour_syzygy_bezout
    thirteenFourSyzygyDegrees thirteenFour_syzygy_degree thirteenFour_syzygy_leading_injective d

theorem thirteenFour_beta_kernel_zero :
    Module.finrank K (boundedObservabilityBetaKernel 3
      (thirteenFourM (K := K)) thirteenFourP 8) = 0 := by
  apply Nat.eq_zero_of_le_zero
  simpa [thirteenFourSyzygyDegrees,Fin.sum_univ_succ] using
    (thirteenFour_beta_kernel_bound (K := K) 8)

theorem thirteenFour_beta_kernel_nine_le :
    Module.finrank K (boundedObservabilityBetaKernel 3
      (thirteenFourM (K := K)) thirteenFourP 9) ≤ 2 := by
  simpa [thirteenFourSyzygyDegrees,Fin.sum_univ_succ] using
    (thirteenFour_beta_kernel_bound (K := K) 9)

end FD56
