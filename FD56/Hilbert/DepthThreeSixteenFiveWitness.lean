/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthThreeSixteenFiveSyzygyData
import FD56.Hilbert.ObservabilityBetaVectorBound

/-! Exact auxiliary-kernel bounds for sixteen states and five rows. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K : Type*} [Field K]
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 400000

def sixteenFiveM0 : Matrix (Fin 16) (Fin 16) K :=
  (sixteenFiveM (K := K)).map (Polynomial.evalRingHom 0)

theorem sixteenFive_evalM :
    (sixteenFiveM (K := K)).map (Polynomial.evalRingHom 0) = sixteenFiveM0 := rfl

def sixteenFiveP0 : Matrix (Fin 5) (Fin 16) K :=
  (sixteenFiveP (K := K)).map (Polynomial.evalRingHom 0)

theorem sixteenFive_evalP :
    (sixteenFiveP (K := K)).map (Polynomial.evalRingHom 0) = sixteenFiveP0 := rfl

def sixteenFiveSelector : Fin 3 → Fin 5 → Fin 16 :=
  ![![⟨0,by decide⟩,⟨3,by decide⟩,⟨6,by decide⟩,⟨9,by decide⟩,⟨12,by decide⟩],
    ![⟨1,by decide⟩,⟨4,by decide⟩,⟨7,by decide⟩,⟨10,by decide⟩,⟨13,by decide⟩],
    ![⟨2,by decide⟩,⟨5,by decide⟩,⟨8,by decide⟩,⟨11,by decide⟩,⟨14,by decide⟩]]

def sixteenFiveRow : Fin 3 × Fin 5 → Fin 16 := fun i => sixteenFiveSelector i.1 i.2

def sixteenFiveConstantBlock (i : Fin 3) : Matrix (Fin 5) (Fin 16) K :=
  (1 : Matrix (Fin 16) (Fin 16) K).submatrix (sixteenFiveSelector i) id

def sixteenFiveO0 : Matrix (Fin 3 × Fin 5) (Fin 16) K :=
  (1 : Matrix (Fin 16) (Fin 16) K).submatrix sixteenFiveRow id

def sixteenFiveR0 : Matrix (Fin 16) (Fin 3 × Fin 5) K :=
  (1 : Matrix (Fin 16) (Fin 16) K).submatrix id sixteenFiveRow

theorem sixteenFive_P0_eq :
    sixteenFiveP0 (K := K) = sixteenFiveConstantBlock 0 := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals first
    | change (Polynomial.evalRingHom (0 : K)) (0 : K[X]) = 0
    | change (Polynomial.evalRingHom (0 : K)) (1 : K[X]) = 1
    | change (Polynomial.evalRingHom (0 : K)) (X : K[X]) = 0
  all_goals simp

theorem sixteenFive_constant_step (i : Fin 2) :
    sixteenFiveConstantBlock (K := K) i.castSucc * sixteenFiveM0 (K := K) =
      sixteenFiveConstantBlock i.succ := by
  calc
    _ = (sixteenFiveM0 (K := K)).submatrix (sixteenFiveSelector i.castSucc) id := by
      simpa only [sixteenFiveConstantBlock,Equiv.refl_apply,Function.id_comp] using
        Matrix.one_submatrix_mul (sixteenFiveSelector i.castSucc)
          (Equiv.refl (Fin 16)) (sixteenFiveM0 (K := K))
    _ = _ := by
      ext a j
      fin_cases i <;> fin_cases a <;> fin_cases j
      all_goals first
        | change (Polynomial.evalRingHom (0 : K)) (0 : K[X]) = 0
        | change (Polynomial.evalRingHom (0 : K)) (1 : K[X]) = 1
        | change (Polynomial.evalRingHom (0 : K)) (X : K[X]) = 0
      all_goals simp

theorem sixteenFive_evalO :
    (observabilityMatrix (sixteenFiveM (K := K)) sixteenFiveP 3).map
      (Polynomial.evalRingHom 0) = sixteenFiveO0 := by
  have h0 := sixteenFive_constant_step (K := K) 0
  have h1 := sixteenFive_constant_step (K := K) 1
  change sixteenFiveConstantBlock (K := K) 0 * sixteenFiveM0 = sixteenFiveConstantBlock 1 at h0
  change sixteenFiveConstantBlock (K := K) 1 * sixteenFiveM0 = sixteenFiveConstantBlock 2 at h1
  rw [observabilityMatrix_map,sixteenFive_evalM,sixteenFive_evalP,sixteenFive_P0_eq]
  funext i j
  rcases i with ⟨i,a⟩
  change (sixteenFiveConstantBlock (K := K) 0 * sixteenFiveM0 (K := K)^i.val) a j =
    sixteenFiveConstantBlock i a j
  fin_cases i
  · simp only [Fin.val_zero,pow_zero,Matrix.mul_one]
    rfl
  · simpa only [Fin.val_one,pow_one] using congrFun (congrFun h0 a) j
  · simp only [Fin.val_two,pow_two,← Matrix.mul_assoc]
    rw [h0,h1]
    rfl

theorem sixteenFive_constant_right_inverse :
    (observabilityMatrix (sixteenFiveM (K := K)) sixteenFiveP 3).map
      (Polynomial.evalRingHom 0) * (sixteenFiveR0 (K := K)) = 1 := by
  rw [sixteenFive_evalO]
  have hr : Function.Injective sixteenFiveRow := by decide
  calc
    _ = (sixteenFiveR0 (K := K)).submatrix sixteenFiveRow id := by
      simpa only [sixteenFiveO0,Equiv.refl_apply,Function.id_comp] using
        Matrix.one_submatrix_mul sixteenFiveRow (Equiv.refl (Fin 16)) (sixteenFiveR0 (K := K))
    _ = 1 := by
      ext i j
      simp [sixteenFiveR0,Matrix.submatrix_apply,Matrix.one_apply,hr.eq_iff]

theorem sixteenFive_stack_injective :
    Function.Injective (observabilityMatrix (sixteenFiveM (K := K)) sixteenFiveP 3).transpose.mulVec := by
  apply polynomial_matrix_injective_of_zero
  rw [Matrix.transpose_map]
  apply matrix_transpose_injective_of_surjective
  intro v
  refine ⟨sixteenFiveR0 *ᵥ v,?_⟩
  rw [Matrix.mulVec_mulVec,sixteenFive_constant_right_inverse,Matrix.one_mulVec]

theorem sixteenFive_stack_vector :
    observabilityMatrix (sixteenFiveM (K := K)) sixteenFiveP 3 *ᵥ sixteenFiveV0 = 0 := by
  funext i
  rcases i with ⟨i,a⟩
  change ((sixteenFiveP * sixteenFiveM^i.val) *ᵥ sixteenFiveV0) a = 0
  fin_cases i
  · simpa only [Fin.val_zero,pow_zero,Matrix.mul_one] using congrFun (sixteenFive_output0 (K := K)) a
  · simpa only [Fin.val_one,pow_one,← Matrix.mulVec_mulVec,sixteenFive_step0] using
      congrFun (sixteenFive_output1 (K := K)) a
  · simpa only [Fin.val_two,pow_two,← Matrix.mulVec_mulVec,sixteenFive_step0,sixteenFive_step1] using
      congrFun (sixteenFive_output2 (K := K)) a

theorem sixteenFive_terminal_vector :
    (sixteenFiveP (K := K)*sixteenFiveM^3) *ᵥ sixteenFiveV0 = sixteenFiveF := by
  simpa only [pow_succ,pow_zero,Matrix.one_mul,← Matrix.mulVec_mulVec,
    sixteenFive_step0,sixteenFive_step1,sixteenFive_step2] using (sixteenFive_output3 (K := K))

variable [CharZero K]

theorem sixteenFive_beta_kernel_bound (d : ℕ) :
    Module.finrank K (boundedObservabilityBetaKernel 3
      (sixteenFiveM (K := K)) sixteenFiveP d) ≤
      ∑ j : Fin 4, (d + 1 - sixteenFiveSyzygyDegrees j) := by
  exact observability_beta_finrank_le_scaled_cofactors 3 sixteenFiveM sixteenFiveP
    sixteenFiveV0 sixteenFiveF sixteenFive_terminal_vector sixteenFive_stack_vector
    sixteenFive_stack_injective sixteenFiveSyzygy sixteenFiveBezout
    (-33416268238642265571948) 1164239739686769372097826095241 (by norm_num) (by norm_num)
    sixteenFive_syzygy_cofactors sixteenFive_syzygy_bezout
    sixteenFiveSyzygyDegrees sixteenFive_syzygy_degree sixteenFive_syzygy_leading_injective d

theorem sixteenFive_beta_kernel_zero :
    Module.finrank K (boundedObservabilityBetaKernel 3
      (sixteenFiveM (K := K)) sixteenFiveP 7) = 0 := by
  apply Nat.eq_zero_of_le_zero
  simpa [sixteenFiveSyzygyDegrees,Fin.sum_univ_succ] using
    (sixteenFive_beta_kernel_bound (K := K) 7)

theorem sixteenFive_beta_kernel_eight_le :
    Module.finrank K (boundedObservabilityBetaKernel 3
      (sixteenFiveM (K := K)) sixteenFiveP 8) ≤ 2 := by
  simpa [sixteenFiveSyzygyDegrees,Fin.sum_univ_succ] using
    (sixteenFive_beta_kernel_bound (K := K) 8)

end FD56
