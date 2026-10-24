/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.CubicScalarInduction
import FD56.Hilbert.FiniteMatrixEvaluation
import Mathlib.Tactic.LinearCombination

/-! Exact scalar obstruction identities for the three-high-column base with 2 low columns. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option maxRecDepth 4096

variable {K : Type*} [Field K] [CharZero K]

def mixedOneThreeBase2 : Matrix (Fin 8) (Fin 5) K[X] :=
  ![![X^3,0,0,0,0],
    ![0,X^3,0,0,0],
    ![0,0,X^4,0,0],
    ![-1,0,1,X^4,0],
    ![0,-1,0,1+X,X^4],
    ![0,0,-1,X^3,-X^3],
    ![0,0,0,-1,X^2+X^3],
    ![0,0,0,0,-1]]

omit [CharZero K] in
private theorem scalar_relation_coeff
    (E : Matrix (Fin 5) (Fin 8) K[X]) (c : K[X])
    (hrel : E*mixedOneThreeBase2=(-c) • (1 : Matrix (Fin 5) (Fin 5) K[X]))
    (i j : Fin 5) (k : ℕ) :
    ((E*mixedOneThreeBase2 (K := K)) i j).coeff k+(if i=j then c.coeff k else 0)=0 := by
  have h := congrArg (fun Z : Matrix (Fin 5) (Fin 5) K[X] => (Z i j).coeff k) hrel
  by_cases hij : i=j
  · simp [Matrix.smul_apply,Matrix.one_apply,hij] at h ⊢
    exact add_eq_zero_iff_eq_neg.mpr h
  · simpa [Matrix.smul_apply,Matrix.one_apply,hij] using h

set_option maxHeartbeats 1200000 in
theorem mixedOneThreeBase2_critical
    (E : Matrix (Fin 5) (Fin 8) K[X]) (c : K[X])
    (hE : ∀ i x, (E i x).natDegree ≤ (if i.val < 2 then 5 else 4))
    (hc : c.natDegree≤8)
    (hrel : E*mixedOneThreeBase2=(-c) • (1 : Matrix (Fin 5) (Fin 5) K[X]))
    : c=0 := by
  have hz0 (x : Fin 8) (k : ℕ) (hk : 5<k) : (E 0 x).coeff k=0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (by simpa using hE 0 x) hk)
  have hz1 (x : Fin 8) (k : ℕ) (hk : 5<k) : (E 1 x).coeff k=0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (by simpa using hE 1 x) hk)
  have hz2 (x : Fin 8) (k : ℕ) (hk : 4<k) : (E 2 x).coeff k=0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (by simpa using hE 2 x) hk)
  have hz3 (x : Fin 8) (k : ℕ) (hk : 4<k) : (E 3 x).coeff k=0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (by simpa using hE 3 x) hk)
  have hz4 (x : Fin 8) (k : ℕ) (hk : 4<k) : (E 4 x).coeff k=0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (by simpa using hE 4 x) hk)
  have h (i j : Fin 5) (k : ℕ) := scalar_relation_coeff E c hrel i j k
  have h_2_0_0 : -(E 2 3).coeff 0=0 := by
    have hh := h 2 0 0
    rw [if_neg (show (2 : Fin 5) ≠ 0 by decide)] at hh
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_2_0_1 : -(E 2 3).coeff 1=0 := by
    have hh := h 2 0 1
    rw [if_neg (show (2 : Fin 5) ≠ 0 by decide)] at hh
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_2_0_2 : -(E 2 3).coeff 2=0 := by
    have hh := h 2 0 2
    rw [if_neg (show (2 : Fin 5) ≠ 0 by decide)] at hh
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_2_1_1 : -(E 2 4).coeff 1=0 := by
    have hh := h 2 1 1
    rw [if_neg (show (2 : Fin 5) ≠ 1 by decide)] at hh
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_2_1_2 : -(E 2 4).coeff 2=0 := by
    have hh := h 2 1 2
    rw [if_neg (show (2 : Fin 5) ≠ 1 by decide)] at hh
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_2_2_0 : (E 2 3).coeff 0 + -(E 2 5).coeff 0 + c.coeff 0=0 := by
    have hh := h 2 2 0
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_2_2_1 : (E 2 3).coeff 1 + -(E 2 5).coeff 1 + c.coeff 1=0 := by
    have hh := h 2 2 1
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_2_2_2 : (E 2 3).coeff 2 + -(E 2 5).coeff 2 + c.coeff 2=0 := by
    have hh := h 2 2 2
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_2_2_3 : (E 2 3).coeff 3 + -(E 2 5).coeff 3 + c.coeff 3=0 := by
    have hh := h 2 2 3
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_2_3_2 : (E 2 4).coeff 2 + (E 2 4).coeff 1 + -(E 2 6).coeff 2=0 := by
    have hh := h 2 3 2
    rw [if_neg (show (2 : Fin 5) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_2_3_3 : (E 2 4).coeff 3 + (E 2 4).coeff 2 + (E 2 5).coeff 0 + -(E 2 6).coeff 3=0 := by
    have hh := h 2 3 3
    rw [if_neg (show (2 : Fin 5) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_2_3_4 : (E 2 3).coeff 0 + (E 2 4).coeff 4 + (E 2 4).coeff 3 + (E 2 5).coeff 1 + -(E 2 6).coeff 4=0 := by
    have hh := h 2 3 4
    rw [if_neg (show (2 : Fin 5) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_2_3_5 : (E 2 3).coeff 1 + (E 2 4).coeff 4 + (E 2 5).coeff 2=0 := by
    have hh := h 2 3 5
    rw [if_neg (show (2 : Fin 5) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_2_3_6 : (E 2 3).coeff 2 + (E 2 5).coeff 3=0 := by
    have hh := h 2 3 6
    rw [if_neg (show (2 : Fin 5) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_2_3_7 : (E 2 3).coeff 3 + (E 2 5).coeff 4=0 := by
    have hh := h 2 3 7
    rw [if_neg (show (2 : Fin 5) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_2_4_5 : (E 2 4).coeff 1 + -(E 2 5).coeff 2 + (E 2 6).coeff 3 + (E 2 6).coeff 2=0 := by
    have hh := h 2 4 5
    rw [if_neg (show (2 : Fin 5) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_2_4_6 : (E 2 4).coeff 2 + -(E 2 5).coeff 3 + (E 2 6).coeff 4 + (E 2 6).coeff 3=0 := by
    have hh := h 2 4 6
    rw [if_neg (show (2 : Fin 5) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_2_4_7 : (E 2 4).coeff 3 + -(E 2 5).coeff 4 + (E 2 6).coeff 4=0 := by
    have hh := h 2 4 7
    rw [if_neg (show (2 : Fin 5) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_2_4_8 : (E 2 4).coeff 4=0 := by
    have hh := h 2 4 8
    rw [if_neg (show (2 : Fin 5) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_0_0 : -(E 3 3).coeff 0=0 := by
    have hh := h 3 0 0
    rw [if_neg (show (3 : Fin 5) ≠ 0 by decide)] at hh
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_0_1 : -(E 3 3).coeff 1=0 := by
    have hh := h 3 0 1
    rw [if_neg (show (3 : Fin 5) ≠ 0 by decide)] at hh
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_0_2 : -(E 3 3).coeff 2=0 := by
    have hh := h 3 0 2
    rw [if_neg (show (3 : Fin 5) ≠ 0 by decide)] at hh
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_1_1 : -(E 3 4).coeff 1=0 := by
    have hh := h 3 1 1
    rw [if_neg (show (3 : Fin 5) ≠ 1 by decide)] at hh
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_1_2 : -(E 3 4).coeff 2=0 := by
    have hh := h 3 1 2
    rw [if_neg (show (3 : Fin 5) ≠ 1 by decide)] at hh
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_2_0 : (E 3 3).coeff 0 + -(E 3 5).coeff 0=0 := by
    have hh := h 3 2 0
    rw [if_neg (show (3 : Fin 5) ≠ 2 by decide)] at hh
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_2_1 : (E 3 3).coeff 1 + -(E 3 5).coeff 1=0 := by
    have hh := h 3 2 1
    rw [if_neg (show (3 : Fin 5) ≠ 2 by decide)] at hh
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_2_2 : (E 3 3).coeff 2 + -(E 3 5).coeff 2=0 := by
    have hh := h 3 2 2
    rw [if_neg (show (3 : Fin 5) ≠ 2 by decide)] at hh
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_2_3 : (E 3 3).coeff 3 + -(E 3 5).coeff 3=0 := by
    have hh := h 3 2 3
    rw [if_neg (show (3 : Fin 5) ≠ 2 by decide)] at hh
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_3_2 : (E 3 4).coeff 2 + (E 3 4).coeff 1 + -(E 3 6).coeff 2 + c.coeff 2=0 := by
    have hh := h 3 3 2
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_3_3 : (E 3 4).coeff 3 + (E 3 4).coeff 2 + (E 3 5).coeff 0 + -(E 3 6).coeff 3 + c.coeff 3=0 := by
    have hh := h 3 3 3
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_3_4 : (E 3 3).coeff 0 + (E 3 4).coeff 4 + (E 3 4).coeff 3 + (E 3 5).coeff 1 + -(E 3 6).coeff 4 + c.coeff 4=0 := by
    have hh := h 3 3 4
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_3_5 : (E 3 3).coeff 1 + (E 3 4).coeff 4 + (E 3 5).coeff 2 + c.coeff 5=0 := by
    have hh := h 3 3 5
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_3_6 : (E 3 3).coeff 2 + (E 3 5).coeff 3 + c.coeff 6=0 := by
    have hh := h 3 3 6
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_3_7 : (E 3 3).coeff 3 + (E 3 5).coeff 4 + c.coeff 7=0 := by
    have hh := h 3 3 7
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_4_5 : (E 3 4).coeff 1 + -(E 3 5).coeff 2 + (E 3 6).coeff 3 + (E 3 6).coeff 2=0 := by
    have hh := h 3 4 5
    rw [if_neg (show (3 : Fin 5) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_4_6 : (E 3 4).coeff 2 + -(E 3 5).coeff 3 + (E 3 6).coeff 4 + (E 3 6).coeff 3=0 := by
    have hh := h 3 4 6
    rw [if_neg (show (3 : Fin 5) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_4_7 : (E 3 4).coeff 3 + -(E 3 5).coeff 4 + (E 3 6).coeff 4=0 := by
    have hh := h 3 4 7
    rw [if_neg (show (3 : Fin 5) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_4_8 : (E 3 4).coeff 4=0 := by
    have hh := h 3 4 8
    rw [if_neg (show (3 : Fin 5) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_0_0 : -(E 4 3).coeff 0=0 := by
    have hh := h 4 0 0
    rw [if_neg (show (4 : Fin 5) ≠ 0 by decide)] at hh
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_0_1 : -(E 4 3).coeff 1=0 := by
    have hh := h 4 0 1
    rw [if_neg (show (4 : Fin 5) ≠ 0 by decide)] at hh
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_0_2 : -(E 4 3).coeff 2=0 := by
    have hh := h 4 0 2
    rw [if_neg (show (4 : Fin 5) ≠ 0 by decide)] at hh
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_1_1 : -(E 4 4).coeff 1=0 := by
    have hh := h 4 1 1
    rw [if_neg (show (4 : Fin 5) ≠ 1 by decide)] at hh
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_1_2 : -(E 4 4).coeff 2=0 := by
    have hh := h 4 1 2
    rw [if_neg (show (4 : Fin 5) ≠ 1 by decide)] at hh
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_2_0 : (E 4 3).coeff 0 + -(E 4 5).coeff 0=0 := by
    have hh := h 4 2 0
    rw [if_neg (show (4 : Fin 5) ≠ 2 by decide)] at hh
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_2_1 : (E 4 3).coeff 1 + -(E 4 5).coeff 1=0 := by
    have hh := h 4 2 1
    rw [if_neg (show (4 : Fin 5) ≠ 2 by decide)] at hh
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_2_2 : (E 4 3).coeff 2 + -(E 4 5).coeff 2=0 := by
    have hh := h 4 2 2
    rw [if_neg (show (4 : Fin 5) ≠ 2 by decide)] at hh
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_2_3 : (E 4 3).coeff 3 + -(E 4 5).coeff 3=0 := by
    have hh := h 4 2 3
    rw [if_neg (show (4 : Fin 5) ≠ 2 by decide)] at hh
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_3_2 : (E 4 4).coeff 2 + (E 4 4).coeff 1 + -(E 4 6).coeff 2=0 := by
    have hh := h 4 3 2
    rw [if_neg (show (4 : Fin 5) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_3_3 : (E 4 4).coeff 3 + (E 4 4).coeff 2 + (E 4 5).coeff 0 + -(E 4 6).coeff 3=0 := by
    have hh := h 4 3 3
    rw [if_neg (show (4 : Fin 5) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_3_4 : (E 4 3).coeff 0 + (E 4 4).coeff 4 + (E 4 4).coeff 3 + (E 4 5).coeff 1 + -(E 4 6).coeff 4=0 := by
    have hh := h 4 3 4
    rw [if_neg (show (4 : Fin 5) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_3_5 : (E 4 3).coeff 1 + (E 4 4).coeff 4 + (E 4 5).coeff 2=0 := by
    have hh := h 4 3 5
    rw [if_neg (show (4 : Fin 5) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_3_6 : (E 4 3).coeff 2 + (E 4 5).coeff 3=0 := by
    have hh := h 4 3 6
    rw [if_neg (show (4 : Fin 5) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_3_7 : (E 4 3).coeff 3 + (E 4 5).coeff 4=0 := by
    have hh := h 4 3 7
    rw [if_neg (show (4 : Fin 5) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_4_5 : (E 4 4).coeff 1 + -(E 4 5).coeff 2 + (E 4 6).coeff 3 + (E 4 6).coeff 2 + c.coeff 5=0 := by
    have hh := h 4 4 5
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_4_6 : (E 4 4).coeff 2 + -(E 4 5).coeff 3 + (E 4 6).coeff 4 + (E 4 6).coeff 3 + c.coeff 6=0 := by
    have hh := h 4 4 6
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_4_7 : (E 4 4).coeff 3 + -(E 4 5).coeff 4 + (E 4 6).coeff 4 + c.coeff 7=0 := by
    have hh := h 4 4 7
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_4_8 : (E 4 4).coeff 4 + c.coeff 8=0 := by
    have hh := h 4 4 8
    norm_num [mixedOneThreeBase2,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have hc0 : c.coeff 0=0 := by
    linear_combination (2)*h_2_0_2 + (2)*h_2_1_2 + h_2_2_0 + h_2_3_3 + (2)*h_2_3_6 + h_2_4_6 + h_2_0_0 + h_2_2_3 + -h_2_3_7 + -h_2_4_7 + (-2)*h_3_1_2 + -h_3_2_0 + (2)*h_3_2_2 + -h_3_3_3 + (2)*h_3_3_5 + (-2)*h_3_3_6 + -h_3_4_6 + -h_3_0_0 + -h_3_2_3 + h_3_3_7 + h_3_4_7 + (2)*h_3_0_1 + (-2)*h_3_4_8 + (4)*h_4_0_2 + (-4)*h_4_1_1 + h_4_2_1 + h_4_2_2 + (-2)*h_4_3_2 + h_4_3_4 + -h_4_3_5 + (3)*h_4_3_6 + (-2)*h_4_4_5 + (2)*h_4_4_6 + h_4_0_0 + h_4_2_3 + -h_4_3_7 + -h_4_4_7
  have hc1 : c.coeff 1=0 := by
    linear_combination (3)*h_2_0_2 + (-4)*h_2_1_1 + h_2_2_1 + (-2)*h_2_3_2 + h_2_3_4 + (-2)*h_2_3_5 + (3)*h_2_3_6 + (-2)*h_2_4_5 + (2)*h_2_4_6 + h_2_0_0 + h_2_2_3 + -h_2_3_7 + -h_2_4_7 + -h_2_0_1 + h_2_4_8 + (-2)*h_3_1_2 + -h_3_2_0 + (2)*h_3_2_2 + -h_3_3_3 + (2)*h_3_3_5 + (-2)*h_3_3_6 + -h_3_4_6 + -h_3_0_0 + -h_3_2_3 + h_3_3_7 + h_3_4_7 + (2)*h_3_0_1 + (-2)*h_3_4_8 + (4)*h_4_0_2 + (-4)*h_4_1_1 + h_4_2_1 + h_4_2_2 + (-2)*h_4_3_2 + h_4_3_4 + -h_4_3_5 + (3)*h_4_3_6 + (-2)*h_4_4_5 + (2)*h_4_4_6 + h_4_0_0 + h_4_2_3 + -h_4_3_7 + -h_4_4_7
  have hc2 : c.coeff 2=0 := by
    linear_combination h_2_0_2 + h_2_2_2 + h_2_3_5 + h_2_0_1 + -h_2_4_8
  have hc3 : c.coeff 3=0 := by
    linear_combination (2)*h_3_1_2 + h_3_2_0 + (-2)*h_3_2_2 + h_3_3_3 + (-2)*h_3_3_5 + (2)*h_3_3_6 + h_3_4_6 + h_3_0_0 + h_3_2_3 + -h_3_3_7 + -h_3_4_7 + (-2)*h_3_0_1 + (2)*h_3_4_8 + (-4)*h_4_0_2 + (4)*h_4_1_1 + -h_4_2_1 + -h_4_2_2 + (2)*h_4_3_2 + -h_4_3_4 + h_4_3_5 + (-3)*h_4_3_6 + (2)*h_4_4_5 + (-2)*h_4_4_6 + -h_4_0_0 + -h_4_2_3 + h_4_3_7 + h_4_4_7
  have hc4 : c.coeff 4=0 := by
    linear_combination (2)*h_2_0_2 + (2)*h_2_2_2 + (2)*h_2_3_5 + (2)*h_2_0_1 + (-2)*h_2_4_8 + h_3_0_2 + (-4)*h_3_1_1 + h_3_2_1 + (-2)*h_3_2_2 + (-2)*h_3_3_2 + h_3_3_4 + (-4)*h_3_3_5 + (3)*h_3_3_6 + (-2)*h_3_4_5 + (2)*h_3_4_6 + h_3_0_0 + h_3_2_3 + -h_3_3_7 + -h_3_4_7 + (-3)*h_3_0_1 + (3)*h_3_4_8 + (-6)*h_4_0_2 + (8)*h_4_1_1 + (2)*h_4_1_2 + h_4_2_0 + (-2)*h_4_2_1 + (-2)*h_4_2_2 + (4)*h_4_3_2 + h_4_3_3 + (-2)*h_4_3_4 + (2)*h_4_3_5 + (-4)*h_4_3_6 + (4)*h_4_4_5 + (-3)*h_4_4_6 + -h_4_0_0 + -h_4_2_3 + h_4_3_7 + h_4_4_7
  have hc5 : c.coeff 5=0 := by
    linear_combination h_3_0_2 + h_3_2_2 + h_3_3_5 + h_3_0_1 + -h_3_4_8
  have hc6 : c.coeff 6=0 := by
    linear_combination (2)*h_3_0_2 + (2)*h_3_2_2 + (2)*h_3_3_5 + (2)*h_3_0_1 + (-2)*h_3_4_8 + (2)*h_4_0_2 + (-4)*h_4_1_1 + (-2)*h_4_1_2 + -h_4_2_0 + h_4_2_1 + h_4_2_2 + (-2)*h_4_3_2 + -h_4_3_3 + h_4_3_4 + -h_4_3_5 + h_4_3_6 + (-2)*h_4_4_5 + h_4_4_6
  have hc7 : c.coeff 7=0 := by
    linear_combination (2)*h_3_0_2 + (2)*h_3_2_2 + (2)*h_3_3_5 + (2)*h_3_0_1 + (-2)*h_3_4_8 + (-4)*h_4_1_1 + (-4)*h_4_1_2 + (-2)*h_4_2_0 + h_4_2_1 + h_4_2_2 + (-2)*h_4_3_2 + (-2)*h_4_3_3 + h_4_3_4 + -h_4_3_5 + -h_4_3_6 + (-2)*h_4_4_5 + -h_4_0_0 + -h_4_2_3 + h_4_3_7 + h_4_4_7
  have hc8 : c.coeff 8=0 := by
    linear_combination -h_4_0_2 + -h_4_2_2 + -h_4_3_5 + -h_4_0_1 + h_4_4_8
  apply Polynomial.ext
  intro k
  by_cases hk : k≤8
  · interval_cases k <;> simp [hc0,hc1,hc2,hc3,hc4,hc5,hc6,hc7,hc8]
  · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hc (by omega)),coeff_zero]

end FD56
