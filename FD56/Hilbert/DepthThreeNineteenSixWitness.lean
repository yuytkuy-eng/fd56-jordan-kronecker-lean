/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthThreeNineteenSixSyzygyData
import FD56.Hilbert.ObservabilityBetaVectorBound

/-! Exact auxiliary-kernel bounds for nineteen states and six rows. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K : Type*} [Field K]
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 400000

def nineteenSixM0 : Matrix (Fin 19) (Fin 19) K :=
  (nineteenSixM (K := K)).map (Polynomial.evalRingHom 0)

theorem nineteenSix_evalM :
    (nineteenSixM (K := K)).map (Polynomial.evalRingHom 0) = nineteenSixM0 := rfl

def nineteenSixP0 : Matrix (Fin 6) (Fin 19) K :=
  (nineteenSixP (K := K)).map (Polynomial.evalRingHom 0)

theorem nineteenSix_evalP :
    (nineteenSixP (K := K)).map (Polynomial.evalRingHom 0) = nineteenSixP0 := rfl

def nineteenSixSelector : Fin 3 → Fin 6 → Fin 19 :=
  ![![⟨0,by decide⟩,⟨3,by decide⟩,⟨6,by decide⟩,⟨9,by decide⟩,⟨12,by decide⟩,⟨15,by decide⟩],
    ![⟨1,by decide⟩,⟨4,by decide⟩,⟨7,by decide⟩,⟨10,by decide⟩,⟨13,by decide⟩,⟨16,by decide⟩],
    ![⟨2,by decide⟩,⟨5,by decide⟩,⟨8,by decide⟩,⟨11,by decide⟩,⟨14,by decide⟩,⟨17,by decide⟩]]

def nineteenSixRow : Fin 3 × Fin 6 → Fin 19 := fun i => nineteenSixSelector i.1 i.2

def nineteenSixConstantBlock (i : Fin 3) : Matrix (Fin 6) (Fin 19) K :=
  (1 : Matrix (Fin 19) (Fin 19) K).submatrix (nineteenSixSelector i) id

def nineteenSixO0 : Matrix (Fin 3 × Fin 6) (Fin 19) K :=
  (1 : Matrix (Fin 19) (Fin 19) K).submatrix nineteenSixRow id

def nineteenSixR0 : Matrix (Fin 19) (Fin 3 × Fin 6) K :=
  (1 : Matrix (Fin 19) (Fin 19) K).submatrix id nineteenSixRow

theorem nineteenSix_P0_eq :
    nineteenSixP0 (K := K) = nineteenSixConstantBlock 0 := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals first
    | change (Polynomial.evalRingHom (0 : K)) (0 : K[X]) = 0
    | change (Polynomial.evalRingHom (0 : K)) (1 : K[X]) = 1
    | change (Polynomial.evalRingHom (0 : K)) (X : K[X]) = 0
  all_goals simp

theorem nineteenSix_constant_step (i : Fin 2) :
    nineteenSixConstantBlock (K := K) i.castSucc * nineteenSixM0 (K := K) =
      nineteenSixConstantBlock i.succ := by
  calc
    _ = (nineteenSixM0 (K := K)).submatrix (nineteenSixSelector i.castSucc) id := by
      simpa only [nineteenSixConstantBlock,Equiv.refl_apply,Function.id_comp] using
        Matrix.one_submatrix_mul (nineteenSixSelector i.castSucc)
          (Equiv.refl (Fin 19)) (nineteenSixM0 (K := K))
    _ = _ := by
      ext a j
      fin_cases i <;> fin_cases a <;> fin_cases j
      all_goals first
        | change (Polynomial.evalRingHom (0 : K)) (0 : K[X]) = 0
        | change (Polynomial.evalRingHom (0 : K)) (1 : K[X]) = 1
        | change (Polynomial.evalRingHom (0 : K)) (X : K[X]) = 0
      all_goals simp

theorem nineteenSix_evalO :
    (observabilityMatrix (nineteenSixM (K := K)) nineteenSixP 3).map
      (Polynomial.evalRingHom 0) = nineteenSixO0 := by
  have h0 := nineteenSix_constant_step (K := K) 0
  have h1 := nineteenSix_constant_step (K := K) 1
  change nineteenSixConstantBlock (K := K) 0 * nineteenSixM0 = nineteenSixConstantBlock 1 at h0
  change nineteenSixConstantBlock (K := K) 1 * nineteenSixM0 = nineteenSixConstantBlock 2 at h1
  rw [observabilityMatrix_map,nineteenSix_evalM,nineteenSix_evalP,nineteenSix_P0_eq]
  funext i j
  rcases i with ⟨i,a⟩
  change (nineteenSixConstantBlock (K := K) 0 * nineteenSixM0 (K := K)^i.val) a j =
    nineteenSixConstantBlock i a j
  fin_cases i
  · simp only [Fin.val_zero,pow_zero,Matrix.mul_one]
    rfl
  · simpa only [Fin.val_one,pow_one] using congrFun (congrFun h0 a) j
  · simp only [Fin.val_two,pow_two,← Matrix.mul_assoc]
    rw [h0,h1]
    rfl

theorem nineteenSix_constant_right_inverse :
    (observabilityMatrix (nineteenSixM (K := K)) nineteenSixP 3).map
      (Polynomial.evalRingHom 0) * (nineteenSixR0 (K := K)) = 1 := by
  rw [nineteenSix_evalO]
  have hr : Function.Injective nineteenSixRow := by decide
  calc
    _ = (nineteenSixR0 (K := K)).submatrix nineteenSixRow id := by
      simpa only [nineteenSixO0,Equiv.refl_apply,Function.id_comp] using
        Matrix.one_submatrix_mul nineteenSixRow (Equiv.refl (Fin 19)) (nineteenSixR0 (K := K))
    _ = 1 := by
      ext i j
      simp [nineteenSixR0,Matrix.submatrix_apply,Matrix.one_apply,hr.eq_iff]

theorem nineteenSix_stack_injective :
    Function.Injective (observabilityMatrix (nineteenSixM (K := K)) nineteenSixP 3).transpose.mulVec := by
  apply polynomial_matrix_injective_of_zero
  rw [Matrix.transpose_map]
  apply matrix_transpose_injective_of_surjective
  intro v
  refine ⟨nineteenSixR0 *ᵥ v,?_⟩
  rw [Matrix.mulVec_mulVec,nineteenSix_constant_right_inverse,Matrix.one_mulVec]

theorem nineteenSix_stack_vector :
    observabilityMatrix (nineteenSixM (K := K)) nineteenSixP 3 *ᵥ nineteenSixV0 = 0 := by
  funext i
  rcases i with ⟨i,a⟩
  change ((nineteenSixP * nineteenSixM^i.val) *ᵥ nineteenSixV0) a = 0
  fin_cases i
  · simpa only [Fin.val_zero,pow_zero,Matrix.mul_one] using congrFun (nineteenSix_output0 (K := K)) a
  · simpa only [Fin.val_one,pow_one,← Matrix.mulVec_mulVec,nineteenSix_step0] using
      congrFun (nineteenSix_output1 (K := K)) a
  · simpa only [Fin.val_two,pow_two,← Matrix.mulVec_mulVec,nineteenSix_step0,nineteenSix_step1] using
      congrFun (nineteenSix_output2 (K := K)) a

theorem nineteenSix_terminal_vector :
    (nineteenSixP (K := K)*nineteenSixM^3) *ᵥ nineteenSixV0 = nineteenSixF := by
  simpa only [pow_succ,pow_zero,Matrix.one_mul,← Matrix.mulVec_mulVec,
    nineteenSix_step0,nineteenSix_step1,nineteenSix_step2] using (nineteenSix_output3 (K := K))

variable [CharZero K]

theorem nineteenSix_beta_kernel_bound (d : ℕ) :
    Module.finrank K (boundedObservabilityBetaKernel 3
      (nineteenSixM (K := K)) nineteenSixP d) ≤
      ∑ j : Fin 5, (d + 1 - nineteenSixSyzygyDegrees j) := by
  exact observability_beta_finrank_le_scaled_cofactors 3 nineteenSixM nineteenSixP
    nineteenSixV0 nineteenSixF nineteenSix_terminal_vector nineteenSix_stack_vector
    nineteenSix_stack_injective nineteenSixSyzygy nineteenSixBezout
    (125291554398096346) 3977492227174985995044479291328354722796955 (by norm_num) (by norm_num)
    nineteenSix_syzygy_cofactors nineteenSix_syzygy_bezout
    nineteenSixSyzygyDegrees nineteenSix_syzygy_degree nineteenSix_syzygy_leading_injective d

theorem nineteenSix_beta_kernel_zero :
    Module.finrank K (boundedObservabilityBetaKernel 3
      (nineteenSixM (K := K)) nineteenSixP 7) = 0 := by
  apply Nat.eq_zero_of_le_zero
  simpa [nineteenSixSyzygyDegrees,Fin.sum_univ_succ] using
    (nineteenSix_beta_kernel_bound (K := K) 7)

end FD56
