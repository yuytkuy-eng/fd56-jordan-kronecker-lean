/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthThreeEighteenFiveRelations
import FD56.Hilbert.ObservabilityBetaMatrixBound

/-! Exact auxiliary-kernel bounds for eighteen states and five rows. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K : Type*} [Field K]
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 400000

def eighteenFiveM0 : Matrix (Fin 18) (Fin 18) K :=
  (eighteenFiveM (K := K)).map (Polynomial.evalRingHom 0)

theorem eighteenFive_evalM :
    (eighteenFiveM (K := K)).map (Polynomial.evalRingHom 0) = eighteenFiveM0 := rfl

def eighteenFiveP0 : Matrix (Fin 5) (Fin 18) K :=
  (eighteenFiveP (K := K)).map (Polynomial.evalRingHom 0)

theorem eighteenFive_evalP :
    (eighteenFiveP (K := K)).map (Polynomial.evalRingHom 0) = eighteenFiveP0 := rfl

def eighteenFiveSelector : Fin 3 → Fin 5 → Fin 18 :=
  ![![0,4,8,12,15],![1,5,9,13,16],![2,6,10,14,17]]

def eighteenFiveRow : Fin 3 × Fin 5 → Fin 18 := fun i => eighteenFiveSelector i.1 i.2

def eighteenFiveConstantBlock (i : Fin 3) : Matrix (Fin 5) (Fin 18) K :=
  (1 : Matrix (Fin 18) (Fin 18) K).submatrix (eighteenFiveSelector i) id

def eighteenFiveO0 : Matrix (Fin 3 × Fin 5) (Fin 18) K :=
  (1 : Matrix (Fin 18) (Fin 18) K).submatrix eighteenFiveRow id

def eighteenFiveR0 : Matrix (Fin 18) (Fin 3 × Fin 5) K :=
  (1 : Matrix (Fin 18) (Fin 18) K).submatrix id eighteenFiveRow

theorem eighteenFive_P0_eq :
    eighteenFiveP0 (K := K) = eighteenFiveConstantBlock 0 := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals first
    | change (Polynomial.evalRingHom (0 : K)) (0 : K[X]) = 0
    | change (Polynomial.evalRingHom (0 : K)) (1 : K[X]) = 1
    | change (Polynomial.evalRingHom (0 : K)) (X : K[X]) = 0
  all_goals simp

theorem eighteenFive_constant_step (i : Fin 2) :
    eighteenFiveConstantBlock (K := K) i.castSucc * eighteenFiveM0 (K := K) =
      eighteenFiveConstantBlock i.succ := by
  calc
    _ = (eighteenFiveM0 (K := K)).submatrix (eighteenFiveSelector i.castSucc) id := by
      simpa only [eighteenFiveConstantBlock,Equiv.refl_apply,Function.id_comp] using
        Matrix.one_submatrix_mul (eighteenFiveSelector i.castSucc)
          (Equiv.refl (Fin 18)) (eighteenFiveM0 (K := K))
    _ = _ := by
      ext a j
      fin_cases i <;> fin_cases a <;> fin_cases j
      all_goals first
        | change (Polynomial.evalRingHom (0 : K)) (0 : K[X]) = 0
        | change (Polynomial.evalRingHom (0 : K)) (1 : K[X]) = 1
        | change (Polynomial.evalRingHom (0 : K)) (X : K[X]) = 0
      all_goals simp

theorem eighteenFive_evalO :
    (observabilityMatrix (eighteenFiveM (K := K)) eighteenFiveP 3).map
      (Polynomial.evalRingHom 0) = eighteenFiveO0 := by
  have h0 := eighteenFive_constant_step (K := K) 0
  have h1 := eighteenFive_constant_step (K := K) 1
  change eighteenFiveConstantBlock (K := K) 0 * eighteenFiveM0 = eighteenFiveConstantBlock 1 at h0
  change eighteenFiveConstantBlock (K := K) 1 * eighteenFiveM0 = eighteenFiveConstantBlock 2 at h1
  rw [observabilityMatrix_map,eighteenFive_evalM,eighteenFive_evalP,eighteenFive_P0_eq]
  funext i j
  rcases i with ⟨i,a⟩
  change (eighteenFiveConstantBlock (K := K) 0 * eighteenFiveM0 (K := K)^i.val) a j =
    eighteenFiveConstantBlock i a j
  fin_cases i
  · simp only [Fin.val_zero,pow_zero,Matrix.mul_one]
    rfl
  · simpa only [Fin.val_one,pow_one] using congrFun (congrFun h0 a) j
  · simp only [Fin.val_two,pow_two,← Matrix.mul_assoc]
    rw [h0,h1]
    rfl

theorem eighteenFive_constant_right_inverse :
    (observabilityMatrix (eighteenFiveM (K := K)) eighteenFiveP 3).map
      (Polynomial.evalRingHom 0) * (eighteenFiveR0 (K := K)) = 1 := by
  rw [eighteenFive_evalO]
  have hr : Function.Injective eighteenFiveRow := by decide
  calc
    _ = (eighteenFiveR0 (K := K)).submatrix eighteenFiveRow id := by
      simpa only [eighteenFiveO0,Equiv.refl_apply,Function.id_comp] using
        Matrix.one_submatrix_mul eighteenFiveRow (Equiv.refl (Fin 18)) (eighteenFiveR0 (K := K))
    _ = 1 := by
      ext i j
      simp [eighteenFiveR0,Matrix.submatrix_apply,Matrix.one_apply,hr.eq_iff]

theorem eighteenFive_stack_injective :
    Function.Injective (observabilityMatrix (eighteenFiveM (K := K)) eighteenFiveP 3).transpose.mulVec := by
  apply polynomial_matrix_injective_of_zero
  rw [Matrix.transpose_map]
  apply matrix_transpose_injective_of_surjective
  intro v
  refine ⟨eighteenFiveR0 *ᵥ v,?_⟩
  rw [Matrix.mulVec_mulVec,eighteenFive_constant_right_inverse,Matrix.one_mulVec]

theorem eighteenFive_stack_matrix :
    observabilityMatrix (eighteenFiveM (K := K)) eighteenFiveP 3 * eighteenFiveV0 (K := K) = 0 := by
  funext i j
  rcases i with ⟨i,a⟩
  change (((eighteenFiveP (K := K) * (eighteenFiveM (K := K))^i.val) *
    eighteenFiveV0 (K := K) : Matrix (Fin 5) (Fin 3) K[X]) a j) = 0
  fin_cases i
  · simpa only [Fin.val_zero,pow_zero,Matrix.mul_one] using
      congrArg (fun B => B a j) (eighteenFive_output0 (K := K))
  · simpa only [Fin.val_one,pow_one,Matrix.mul_assoc,eighteenFive_step0] using
      congrArg (fun B => B a j) (eighteenFive_output1 (K := K))
  · simpa only [Fin.val_two,pow_two,Matrix.mul_assoc,eighteenFive_step0,eighteenFive_step1] using
      congrArg (fun B => B a j) (eighteenFive_output2 (K := K))

theorem eighteenFive_terminal_matrix :
    eighteenFiveP (K := K) * eighteenFiveM^3 * eighteenFiveV0 = eighteenFiveF := by
  simpa only [pow_succ,pow_zero,Matrix.one_mul,Matrix.mul_assoc,
    eighteenFive_step0,eighteenFive_step1,eighteenFive_step2] using (eighteenFive_output3 (K := K))

variable [CharZero K]

theorem eighteenFive_beta_kernel_bound (d : ℕ) :
    Module.finrank K (boundedObservabilityBetaKernel 3
      (eighteenFiveM (K := K)) eighteenFiveP d) ≤ 2*(d+1-21) := by
  have h := observability_beta_finrank_le_matrix_relations 3 (eighteenFiveM (K := K)) eighteenFiveP
    eighteenFiveV0 eighteenFive_stack_matrix eighteenFive_stack_injective d
  rw [eighteenFive_terminal_matrix,eighteenFive_terminal_hilbert] at h
  exact h

theorem eighteenFive_beta_kernel_zero :
    Module.finrank K (boundedObservabilityBetaKernel 3
      (eighteenFiveM (K := K)) eighteenFiveP 20) = 0 := by
  apply Nat.eq_zero_of_le_zero
  simpa using eighteenFive_beta_kernel_bound (K := K) 20

end FD56
