/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthThreeSeventeenFiveRelations
import FD56.Hilbert.ObservabilityBetaMatrixBound

/-! Exact auxiliary-kernel bounds for seventeen states and five rows. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K : Type*} [Field K]
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 400000

def seventeenFiveM0 : Matrix (Fin 17) (Fin 17) K :=
  (seventeenFiveM (K := K)).map (Polynomial.evalRingHom 0)

theorem seventeenFive_evalM :
    (seventeenFiveM (K := K)).map (Polynomial.evalRingHom 0) = seventeenFiveM0 := rfl

def seventeenFiveP0 : Matrix (Fin 5) (Fin 17) K :=
  (seventeenFiveP (K := K)).map (Polynomial.evalRingHom 0)

theorem seventeenFive_evalP :
    (seventeenFiveP (K := K)).map (Polynomial.evalRingHom 0) = seventeenFiveP0 := rfl

def seventeenFiveSelector : Fin 3 → Fin 5 → Fin 17 :=
  ![![0,4,8,11,14],![1,5,9,12,15],![2,6,10,13,16]]

def seventeenFiveRow : Fin 3 × Fin 5 → Fin 17 := fun i => seventeenFiveSelector i.1 i.2

def seventeenFiveConstantBlock (i : Fin 3) : Matrix (Fin 5) (Fin 17) K :=
  (1 : Matrix (Fin 17) (Fin 17) K).submatrix (seventeenFiveSelector i) id

def seventeenFiveO0 : Matrix (Fin 3 × Fin 5) (Fin 17) K :=
  (1 : Matrix (Fin 17) (Fin 17) K).submatrix seventeenFiveRow id

def seventeenFiveR0 : Matrix (Fin 17) (Fin 3 × Fin 5) K :=
  (1 : Matrix (Fin 17) (Fin 17) K).submatrix id seventeenFiveRow

theorem seventeenFive_P0_eq :
    seventeenFiveP0 (K := K) = seventeenFiveConstantBlock 0 := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals first
    | change (Polynomial.evalRingHom (0 : K)) (0 : K[X]) = 0
    | change (Polynomial.evalRingHom (0 : K)) (1 : K[X]) = 1
    | change (Polynomial.evalRingHom (0 : K)) (X : K[X]) = 0
  all_goals simp

theorem seventeenFive_constant_step (i : Fin 2) :
    seventeenFiveConstantBlock (K := K) i.castSucc * seventeenFiveM0 (K := K) =
      seventeenFiveConstantBlock i.succ := by
  calc
    _ = (seventeenFiveM0 (K := K)).submatrix (seventeenFiveSelector i.castSucc) id := by
      simpa only [seventeenFiveConstantBlock,Equiv.refl_apply,Function.id_comp] using
        Matrix.one_submatrix_mul (seventeenFiveSelector i.castSucc)
          (Equiv.refl (Fin 17)) (seventeenFiveM0 (K := K))
    _ = _ := by
      ext a j
      fin_cases i <;> fin_cases a <;> fin_cases j
      all_goals first
        | change (Polynomial.evalRingHom (0 : K)) (0 : K[X]) = 0
        | change (Polynomial.evalRingHom (0 : K)) (1 : K[X]) = 1
        | change (Polynomial.evalRingHom (0 : K)) (X : K[X]) = 0
      all_goals simp

theorem seventeenFive_evalO :
    (observabilityMatrix (seventeenFiveM (K := K)) seventeenFiveP 3).map
      (Polynomial.evalRingHom 0) = seventeenFiveO0 := by
  have h0 := seventeenFive_constant_step (K := K) 0
  have h1 := seventeenFive_constant_step (K := K) 1
  change seventeenFiveConstantBlock (K := K) 0 * seventeenFiveM0 = seventeenFiveConstantBlock 1 at h0
  change seventeenFiveConstantBlock (K := K) 1 * seventeenFiveM0 = seventeenFiveConstantBlock 2 at h1
  rw [observabilityMatrix_map,seventeenFive_evalM,seventeenFive_evalP,seventeenFive_P0_eq]
  funext i j
  rcases i with ⟨i,a⟩
  change (seventeenFiveConstantBlock (K := K) 0 * seventeenFiveM0 (K := K)^i.val) a j =
    seventeenFiveConstantBlock i a j
  fin_cases i
  · simp only [Fin.val_zero,pow_zero,Matrix.mul_one]
    rfl
  · simpa only [Fin.val_one,pow_one] using congrFun (congrFun h0 a) j
  · simp only [Fin.val_two,pow_two,← Matrix.mul_assoc]
    rw [h0,h1]
    rfl

theorem seventeenFive_constant_right_inverse :
    (observabilityMatrix (seventeenFiveM (K := K)) seventeenFiveP 3).map
      (Polynomial.evalRingHom 0) * (seventeenFiveR0 (K := K)) = 1 := by
  rw [seventeenFive_evalO]
  have hr : Function.Injective seventeenFiveRow := by decide
  calc
    _ = (seventeenFiveR0 (K := K)).submatrix seventeenFiveRow id := by
      simpa only [seventeenFiveO0,Equiv.refl_apply,Function.id_comp] using
        Matrix.one_submatrix_mul seventeenFiveRow (Equiv.refl (Fin 17)) (seventeenFiveR0 (K := K))
    _ = 1 := by
      ext i j
      simp [seventeenFiveR0,Matrix.submatrix_apply,Matrix.one_apply,hr.eq_iff]

theorem seventeenFive_stack_injective :
    Function.Injective (observabilityMatrix (seventeenFiveM (K := K)) seventeenFiveP 3).transpose.mulVec := by
  apply polynomial_matrix_injective_of_zero
  rw [Matrix.transpose_map]
  apply matrix_transpose_injective_of_surjective
  intro v
  refine ⟨seventeenFiveR0 *ᵥ v,?_⟩
  rw [Matrix.mulVec_mulVec,seventeenFive_constant_right_inverse,Matrix.one_mulVec]

theorem seventeenFive_stack_matrix :
    observabilityMatrix (seventeenFiveM (K := K)) seventeenFiveP 3 * seventeenFiveV0 (K := K) = 0 := by
  funext i j
  rcases i with ⟨i,a⟩
  change (((seventeenFiveP (K := K) * (seventeenFiveM (K := K))^i.val) *
    seventeenFiveV0 (K := K) : Matrix (Fin 5) (Fin 2) K[X]) a j) = 0
  fin_cases i
  · simpa only [Fin.val_zero,pow_zero,Matrix.mul_one] using
      congrArg (fun B => B a j) (seventeenFive_output0 (K := K))
  · simpa only [Fin.val_one,pow_one,Matrix.mul_assoc,seventeenFive_step0] using
      congrArg (fun B => B a j) (seventeenFive_output1 (K := K))
  · simpa only [Fin.val_two,pow_two,Matrix.mul_assoc,seventeenFive_step0,seventeenFive_step1] using
      congrArg (fun B => B a j) (seventeenFive_output2 (K := K))

theorem seventeenFive_terminal_matrix :
    seventeenFiveP (K := K) * seventeenFiveM^3 * seventeenFiveV0 = seventeenFiveF := by
  simpa only [pow_succ,pow_zero,Matrix.one_mul,Matrix.mul_assoc,
    seventeenFive_step0,seventeenFive_step1,seventeenFive_step2] using (seventeenFive_output3 (K := K))

variable [CharZero K]

theorem seventeenFive_beta_kernel_bound (d : ℕ) :
    Module.finrank K (boundedObservabilityBetaKernel 3
      (seventeenFiveM (K := K)) seventeenFiveP d) ≤ (d+1-12) + 2*(d+1-13) := by
  have h := observability_beta_finrank_le_matrix_relations 3 (seventeenFiveM (K := K)) seventeenFiveP
    seventeenFiveV0 seventeenFive_stack_matrix seventeenFive_stack_injective d
  rw [seventeenFive_terminal_matrix,seventeenFive_terminal_hilbert] at h
  exact h

theorem seventeenFive_beta_kernel_zero :
    Module.finrank K (boundedObservabilityBetaKernel 3
      (seventeenFiveM (K := K)) seventeenFiveP 11) = 0 := by
  apply Nat.eq_zero_of_le_zero
  simpa using seventeenFive_beta_kernel_bound (K := K) 11

theorem seventeenFive_beta_kernel_twelve_le :
    Module.finrank K (boundedObservabilityBetaKernel 3
      (seventeenFiveM (K := K)) seventeenFiveP 12) ≤ 1 := by
  simpa using seventeenFive_beta_kernel_bound (K := K) 12

end FD56
