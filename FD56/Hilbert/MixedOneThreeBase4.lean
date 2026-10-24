/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.CubicScalarInduction
import FD56.Hilbert.FiniteMatrixEvaluation
import Mathlib.Tactic.LinearCombination

/-! Exact scalar obstruction identities for the three-high-column base with 4 low columns. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option maxRecDepth 4096

variable {K : Type*} [Field K] [CharZero K]

def mixedOneThreeBase4 : Matrix (Fin 10) (Fin 7) K[X] :=
  ![![X^3,0,0,0,0,0,0],
    ![0,X^3,0,0,0,0,0],
    ![0,0,X^3,0,0,0,0],
    ![-1,0,0,X^3,0,0,0],
    ![0,-1,0,0,X^4,0,0],
    ![0,0,-1,0,X,X^4,0],
    ![0,0,0,-1,0,X^3,X^4],
    ![0,0,0,0,-1,X^2+X^2,0],
    ![0,0,0,0,0,-1,-X+X^3],
    ![0,0,0,0,0,0,-1]]

omit [CharZero K] in
private theorem scalar_relation_coeff
    (E : Matrix (Fin 7) (Fin 10) K[X]) (c : K[X])
    (hrel : E*mixedOneThreeBase4=(-c) • (1 : Matrix (Fin 7) (Fin 7) K[X]))
    (i j : Fin 7) (k : ℕ) :
    ((E*mixedOneThreeBase4 (K := K)) i j).coeff k+(if i=j then c.coeff k else 0)=0 := by
  have h := congrArg (fun Z : Matrix (Fin 7) (Fin 7) K[X] => (Z i j).coeff k) hrel
  by_cases hij : i=j
  · simp [Matrix.smul_apply,Matrix.one_apply,hij] at h ⊢
    exact add_eq_zero_iff_eq_neg.mpr h
  · simpa [Matrix.smul_apply,Matrix.one_apply,hij] using h

set_option maxHeartbeats 1200000 in
theorem mixedOneThreeBase4_zero
    (E : Matrix (Fin 7) (Fin 10) K[X]) (c : K[X])
    (hE : ∀ i x, (E i x).natDegree ≤ (if i.val < 4 then 6 else 5))
    (hc : c.natDegree≤9)
    (hrel : E*mixedOneThreeBase4=(-c) • (1 : Matrix (Fin 7) (Fin 7) K[X]))
    : c=0 := by
  have hz0 (x : Fin 10) (k : ℕ) (hk : 6<k) : (E 0 x).coeff k=0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (by simpa using hE 0 x) hk)
  have hz1 (x : Fin 10) (k : ℕ) (hk : 6<k) : (E 1 x).coeff k=0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (by simpa using hE 1 x) hk)
  have hz2 (x : Fin 10) (k : ℕ) (hk : 6<k) : (E 2 x).coeff k=0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (by simpa using hE 2 x) hk)
  have hz3 (x : Fin 10) (k : ℕ) (hk : 6<k) : (E 3 x).coeff k=0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (by simpa using hE 3 x) hk)
  have hz4 (x : Fin 10) (k : ℕ) (hk : 5<k) : (E 4 x).coeff k=0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (by simpa using hE 4 x) hk)
  have hz5 (x : Fin 10) (k : ℕ) (hk : 5<k) : (E 5 x).coeff k=0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (by simpa using hE 5 x) hk)
  have hz6 (x : Fin 10) (k : ℕ) (hk : 5<k) : (E 6 x).coeff k=0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (by simpa using hE 6 x) hk)
  have h (i j : Fin 7) (k : ℕ) := scalar_relation_coeff E c hrel i j k
  have h_0_0_0 : -(E 0 3).coeff 0 + c.coeff 0=0 := by
    have hh := h 0 0 0
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_0_1 : -(E 0 3).coeff 1 + c.coeff 1=0 := by
    have hh := h 0 0 1
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_0_2 : -(E 0 3).coeff 2 + c.coeff 2=0 := by
    have hh := h 0 0 2
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_1_0 : -(E 0 4).coeff 0=0 := by
    have hh := h 0 1 0
    rw [if_neg (show (0 : Fin 7) ≠ 1 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_1_1 : -(E 0 4).coeff 1=0 := by
    have hh := h 0 1 1
    rw [if_neg (show (0 : Fin 7) ≠ 1 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_1_2 : -(E 0 4).coeff 2=0 := by
    have hh := h 0 1 2
    rw [if_neg (show (0 : Fin 7) ≠ 1 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_2_0 : -(E 0 5).coeff 0=0 := by
    have hh := h 0 2 0
    rw [if_neg (show (0 : Fin 7) ≠ 2 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_2_1 : -(E 0 5).coeff 1=0 := by
    have hh := h 0 2 1
    rw [if_neg (show (0 : Fin 7) ≠ 2 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_2_2 : -(E 0 5).coeff 2=0 := by
    have hh := h 0 2 2
    rw [if_neg (show (0 : Fin 7) ≠ 2 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_3_1 : -(E 0 6).coeff 1=0 := by
    have hh := h 0 3 1
    rw [if_neg (show (0 : Fin 7) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_3_2 : -(E 0 6).coeff 2=0 := by
    have hh := h 0 3 2
    rw [if_neg (show (0 : Fin 7) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_3_3 : (E 0 3).coeff 0 + -(E 0 6).coeff 3=0 := by
    have hh := h 0 3 3
    rw [if_neg (show (0 : Fin 7) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_3_4 : (E 0 3).coeff 1 + -(E 0 6).coeff 4=0 := by
    have hh := h 0 3 4
    rw [if_neg (show (0 : Fin 7) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_3_5 : (E 0 3).coeff 2 + -(E 0 6).coeff 5=0 := by
    have hh := h 0 3 5
    rw [if_neg (show (0 : Fin 7) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_4_2 : (E 0 5).coeff 1 + -(E 0 7).coeff 2=0 := by
    have hh := h 0 4 2
    rw [if_neg (show (0 : Fin 7) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_4_3 : (E 0 5).coeff 2 + -(E 0 7).coeff 3=0 := by
    have hh := h 0 4 3
    rw [if_neg (show (0 : Fin 7) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_4_4 : (E 0 4).coeff 0 + (E 0 5).coeff 3 + -(E 0 7).coeff 4=0 := by
    have hh := h 0 4 4
    rw [if_neg (show (0 : Fin 7) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_4_5 : (E 0 4).coeff 1 + (E 0 5).coeff 4 + -(E 0 7).coeff 5=0 := by
    have hh := h 0 4 5
    rw [if_neg (show (0 : Fin 7) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_4_6 : (E 0 4).coeff 2 + (E 0 5).coeff 5 + -(E 0 7).coeff 6=0 := by
    have hh := h 0 4 6
    rw [if_neg (show (0 : Fin 7) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_5_4 : (E 0 5).coeff 0 + (E 0 6).coeff 1 + (2)*(E 0 7).coeff 2 + -(E 0 8).coeff 4=0 := by
    have hh := h 0 5 4
    rw [if_neg (show (0 : Fin 7) ≠ 5 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_5_5 : (E 0 5).coeff 1 + (E 0 6).coeff 2 + (2)*(E 0 7).coeff 3 + -(E 0 8).coeff 5=0 := by
    have hh := h 0 5 5
    rw [if_neg (show (0 : Fin 7) ≠ 5 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_5_6 : (E 0 5).coeff 2 + (E 0 6).coeff 3 + (2)*(E 0 7).coeff 4 + -(E 0 8).coeff 6=0 := by
    have hh := h 0 5 6
    rw [if_neg (show (0 : Fin 7) ≠ 5 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_5_7 : (E 0 5).coeff 3 + (E 0 6).coeff 4 + (2)*(E 0 7).coeff 5=0 := by
    have hh := h 0 5 7
    rw [if_neg (show (0 : Fin 7) ≠ 5 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_5_8 : (E 0 5).coeff 4 + (E 0 6).coeff 5 + (2)*(E 0 7).coeff 6=0 := by
    have hh := h 0 5 8
    rw [if_neg (show (0 : Fin 7) ≠ 5 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_5_9 : (E 0 5).coeff 5 + (E 0 6).coeff 6=0 := by
    have hh := h 0 5 9
    rw [if_neg (show (0 : Fin 7) ≠ 5 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_6_7 : (E 0 6).coeff 3 + -(E 0 8).coeff 6 + (E 0 8).coeff 4=0 := by
    have hh := h 0 6 7
    rw [if_neg (show (0 : Fin 7) ≠ 6 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_6_8 : (E 0 6).coeff 4 + (E 0 8).coeff 5=0 := by
    have hh := h 0 6 8
    rw [if_neg (show (0 : Fin 7) ≠ 6 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_6_9 : (E 0 6).coeff 5 + (E 0 8).coeff 6=0 := by
    have hh := h 0 6 9
    rw [if_neg (show (0 : Fin 7) ≠ 6 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_6_10 : (E 0 6).coeff 6=0 := by
    have hh := h 0 6 10
    rw [if_neg (show (0 : Fin 7) ≠ 6 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_0_0 : -(E 3 3).coeff 0=0 := by
    have hh := h 3 0 0
    rw [if_neg (show (3 : Fin 7) ≠ 0 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_0_1 : -(E 3 3).coeff 1=0 := by
    have hh := h 3 0 1
    rw [if_neg (show (3 : Fin 7) ≠ 0 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_0_2 : -(E 3 3).coeff 2=0 := by
    have hh := h 3 0 2
    rw [if_neg (show (3 : Fin 7) ≠ 0 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_1_0 : -(E 3 4).coeff 0=0 := by
    have hh := h 3 1 0
    rw [if_neg (show (3 : Fin 7) ≠ 1 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_1_1 : -(E 3 4).coeff 1=0 := by
    have hh := h 3 1 1
    rw [if_neg (show (3 : Fin 7) ≠ 1 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_1_2 : -(E 3 4).coeff 2=0 := by
    have hh := h 3 1 2
    rw [if_neg (show (3 : Fin 7) ≠ 1 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_2_0 : -(E 3 5).coeff 0=0 := by
    have hh := h 3 2 0
    rw [if_neg (show (3 : Fin 7) ≠ 2 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_2_1 : -(E 3 5).coeff 1=0 := by
    have hh := h 3 2 1
    rw [if_neg (show (3 : Fin 7) ≠ 2 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_2_2 : -(E 3 5).coeff 2=0 := by
    have hh := h 3 2 2
    rw [if_neg (show (3 : Fin 7) ≠ 2 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_3_1 : -(E 3 6).coeff 1 + c.coeff 1=0 := by
    have hh := h 3 3 1
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_3_2 : -(E 3 6).coeff 2 + c.coeff 2=0 := by
    have hh := h 3 3 2
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_3_3 : (E 3 3).coeff 0 + -(E 3 6).coeff 3 + c.coeff 3=0 := by
    have hh := h 3 3 3
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_3_4 : (E 3 3).coeff 1 + -(E 3 6).coeff 4 + c.coeff 4=0 := by
    have hh := h 3 3 4
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_3_5 : (E 3 3).coeff 2 + -(E 3 6).coeff 5 + c.coeff 5=0 := by
    have hh := h 3 3 5
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_4_2 : (E 3 5).coeff 1 + -(E 3 7).coeff 2=0 := by
    have hh := h 3 4 2
    rw [if_neg (show (3 : Fin 7) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_4_3 : (E 3 5).coeff 2 + -(E 3 7).coeff 3=0 := by
    have hh := h 3 4 3
    rw [if_neg (show (3 : Fin 7) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_4_4 : (E 3 4).coeff 0 + (E 3 5).coeff 3 + -(E 3 7).coeff 4=0 := by
    have hh := h 3 4 4
    rw [if_neg (show (3 : Fin 7) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_4_5 : (E 3 4).coeff 1 + (E 3 5).coeff 4 + -(E 3 7).coeff 5=0 := by
    have hh := h 3 4 5
    rw [if_neg (show (3 : Fin 7) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_4_6 : (E 3 4).coeff 2 + (E 3 5).coeff 5 + -(E 3 7).coeff 6=0 := by
    have hh := h 3 4 6
    rw [if_neg (show (3 : Fin 7) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_5_4 : (E 3 5).coeff 0 + (E 3 6).coeff 1 + (2)*(E 3 7).coeff 2 + -(E 3 8).coeff 4=0 := by
    have hh := h 3 5 4
    rw [if_neg (show (3 : Fin 7) ≠ 5 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_5_5 : (E 3 5).coeff 1 + (E 3 6).coeff 2 + (2)*(E 3 7).coeff 3 + -(E 3 8).coeff 5=0 := by
    have hh := h 3 5 5
    rw [if_neg (show (3 : Fin 7) ≠ 5 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_5_6 : (E 3 5).coeff 2 + (E 3 6).coeff 3 + (2)*(E 3 7).coeff 4 + -(E 3 8).coeff 6=0 := by
    have hh := h 3 5 6
    rw [if_neg (show (3 : Fin 7) ≠ 5 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_5_7 : (E 3 5).coeff 3 + (E 3 6).coeff 4 + (2)*(E 3 7).coeff 5=0 := by
    have hh := h 3 5 7
    rw [if_neg (show (3 : Fin 7) ≠ 5 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_5_8 : (E 3 5).coeff 4 + (E 3 6).coeff 5 + (2)*(E 3 7).coeff 6=0 := by
    have hh := h 3 5 8
    rw [if_neg (show (3 : Fin 7) ≠ 5 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_5_9 : (E 3 5).coeff 5 + (E 3 6).coeff 6=0 := by
    have hh := h 3 5 9
    rw [if_neg (show (3 : Fin 7) ≠ 5 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_6_7 : (E 3 6).coeff 3 + -(E 3 8).coeff 6 + (E 3 8).coeff 4=0 := by
    have hh := h 3 6 7
    rw [if_neg (show (3 : Fin 7) ≠ 6 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_6_8 : (E 3 6).coeff 4 + (E 3 8).coeff 5=0 := by
    have hh := h 3 6 8
    rw [if_neg (show (3 : Fin 7) ≠ 6 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_6_9 : (E 3 6).coeff 5 + (E 3 8).coeff 6=0 := by
    have hh := h 3 6 9
    rw [if_neg (show (3 : Fin 7) ≠ 6 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_6_10 : (E 3 6).coeff 6=0 := by
    have hh := h 3 6 10
    rw [if_neg (show (3 : Fin 7) ≠ 6 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_1_2 : -(E 4 4).coeff 2=0 := by
    have hh := h 4 1 2
    rw [if_neg (show (4 : Fin 7) ≠ 1 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_4_6 : (E 4 4).coeff 2 + (E 4 5).coeff 5 + c.coeff 6=0 := by
    have hh := h 4 4 6
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_5_9 : (E 4 5).coeff 5=0 := by
    have hh := h 4 5 9
    rw [if_neg (show (4 : Fin 7) ≠ 5 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_0_0 : -(E 5 3).coeff 0=0 := by
    have hh := h 5 0 0
    rw [if_neg (show (5 : Fin 7) ≠ 0 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_0_1 : -(E 5 3).coeff 1=0 := by
    have hh := h 5 0 1
    rw [if_neg (show (5 : Fin 7) ≠ 0 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_0_2 : -(E 5 3).coeff 2=0 := by
    have hh := h 5 0 2
    rw [if_neg (show (5 : Fin 7) ≠ 0 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_1_0 : -(E 5 4).coeff 0=0 := by
    have hh := h 5 1 0
    rw [if_neg (show (5 : Fin 7) ≠ 1 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_1_1 : -(E 5 4).coeff 1=0 := by
    have hh := h 5 1 1
    rw [if_neg (show (5 : Fin 7) ≠ 1 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_1_2 : -(E 5 4).coeff 2=0 := by
    have hh := h 5 1 2
    rw [if_neg (show (5 : Fin 7) ≠ 1 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_2_2 : -(E 5 5).coeff 2=0 := by
    have hh := h 5 2 2
    rw [if_neg (show (5 : Fin 7) ≠ 2 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_3_3 : (E 5 3).coeff 0 + -(E 5 6).coeff 3=0 := by
    have hh := h 5 3 3
    rw [if_neg (show (5 : Fin 7) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_3_4 : (E 5 3).coeff 1 + -(E 5 6).coeff 4=0 := by
    have hh := h 5 3 4
    rw [if_neg (show (5 : Fin 7) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_3_5 : (E 5 3).coeff 2 + -(E 5 6).coeff 5=0 := by
    have hh := h 5 3 5
    rw [if_neg (show (5 : Fin 7) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_4_4 : (E 5 4).coeff 0 + (E 5 5).coeff 3 + -(E 5 7).coeff 4=0 := by
    have hh := h 5 4 4
    rw [if_neg (show (5 : Fin 7) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_4_5 : (E 5 4).coeff 1 + (E 5 5).coeff 4 + -(E 5 7).coeff 5=0 := by
    have hh := h 5 4 5
    rw [if_neg (show (5 : Fin 7) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_4_6 : (E 5 4).coeff 2 + (E 5 5).coeff 5=0 := by
    have hh := h 5 4 6
    rw [if_neg (show (5 : Fin 7) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_5_6 : (E 5 5).coeff 2 + (E 5 6).coeff 3 + (2)*(E 5 7).coeff 4 + c.coeff 6=0 := by
    have hh := h 5 5 6
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_5_7 : (E 5 5).coeff 3 + (E 5 6).coeff 4 + (2)*(E 5 7).coeff 5 + c.coeff 7=0 := by
    have hh := h 5 5 7
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_5_8 : (E 5 5).coeff 4 + (E 5 6).coeff 5 + c.coeff 8=0 := by
    have hh := h 5 5 8
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_5_9 : (E 5 5).coeff 5 + c.coeff 9=0 := by
    have hh := h 5 5 9
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_6_0_0 : -(E 6 3).coeff 0=0 := by
    have hh := h 6 0 0
    rw [if_neg (show (6 : Fin 7) ≠ 0 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_6_2_0 : -(E 6 5).coeff 0=0 := by
    have hh := h 6 2 0
    rw [if_neg (show (6 : Fin 7) ≠ 2 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_6_2_1 : -(E 6 5).coeff 1=0 := by
    have hh := h 6 2 1
    rw [if_neg (show (6 : Fin 7) ≠ 2 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_6_3_1 : -(E 6 6).coeff 1=0 := by
    have hh := h 6 3 1
    rw [if_neg (show (6 : Fin 7) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_6_3_3 : (E 6 3).coeff 0 + -(E 6 6).coeff 3=0 := by
    have hh := h 6 3 3
    rw [if_neg (show (6 : Fin 7) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_6_4_2 : (E 6 5).coeff 1 + -(E 6 7).coeff 2=0 := by
    have hh := h 6 4 2
    rw [if_neg (show (6 : Fin 7) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_6_5_4 : (E 6 5).coeff 0 + (E 6 6).coeff 1 + (2)*(E 6 7).coeff 2 + -(E 6 8).coeff 4=0 := by
    have hh := h 6 5 4
    rw [if_neg (show (6 : Fin 7) ≠ 5 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_6_6_7 : (E 6 6).coeff 3 + (E 6 8).coeff 4 + c.coeff 7=0 := by
    have hh := h 6 6 7
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have hc0 : c.coeff 0=0 := by
    linear_combination (2)*h_0_2_1 + (-5/4 : K)*h_0_2_2 + (-1/2 : K)*h_0_3_2 + -h_0_4_3 + (-1/2 : K)*h_0_5_5 + (-1/2 : K)*h_0_6_8 + h_0_0_0 + (5/4 : K)*h_0_2_0 + (5/4 : K)*h_0_3_1 + h_0_3_3 + (5/2 : K)*h_0_4_2 + (5/4 : K)*h_0_5_4 + (5/4 : K)*h_0_6_7 + h_0_6_9 + (-1/2 : K)*h_0_1_0 + h_0_1_1 + (-2)*h_0_1_2 + (-1/2 : K)*h_0_4_4 + h_0_4_5 + (-2)*h_0_4_6 + (-1/4 : K)*h_0_5_6 + (1/2 : K)*h_0_5_7 + -h_0_5_8 + (2)*h_0_5_9 + (-2)*h_0_6_10
  have hc1 : c.coeff 1=0 := by
    linear_combination h_0_0_1 + h_0_2_1 + (2)*h_0_2_2 + h_0_3_2 + h_0_3_4 + (2)*h_0_4_3 + h_0_5_5 + h_0_6_8
  have hc2 : c.coeff 2=0 := by
    linear_combination (5/4 : K)*h_0_2_2 + (1/2 : K)*h_0_3_2 + h_0_4_3 + (1/2 : K)*h_0_5_5 + (1/2 : K)*h_0_6_8 + h_0_0_2 + (-1/4 : K)*h_0_2_0 + (-1/4 : K)*h_0_3_1 + h_0_3_5 + (-1/2 : K)*h_0_4_2 + (-1/4 : K)*h_0_5_4 + (-1/4 : K)*h_0_6_7 + (1/2 : K)*h_0_1_0 + -h_0_1_1 + (2)*h_0_1_2 + (1/2 : K)*h_0_4_4 + -h_0_4_5 + (2)*h_0_4_6 + (1/4 : K)*h_0_5_6 + (-1/2 : K)*h_0_5_7 + h_0_5_8 + (-2)*h_0_5_9 + (2)*h_0_6_10
  have hc3 : c.coeff 3=0 := by
    linear_combination (-5/4 : K)*h_0_0_1 + (-5/4 : K)*h_0_2_1 + (-15/8 : K)*h_0_2_2 + -h_0_3_2 + (-5/4 : K)*h_0_3_4 + (-2)*h_0_4_3 + -h_0_5_5 + -h_0_6_8 + (1/2 : K)*h_0_0_2 + (-1/8 : K)*h_0_2_0 + (-1/8 : K)*h_0_3_1 + (1/2 : K)*h_0_3_5 + (-1/4 : K)*h_0_4_2 + (-1/8 : K)*h_0_5_4 + (-1/8 : K)*h_0_6_7 + (1/4 : K)*h_0_1_0 + (-1/2 : K)*h_0_1_1 + h_0_1_2 + (1/4 : K)*h_0_4_4 + (-1/2 : K)*h_0_4_5 + h_0_4_6 + (1/8 : K)*h_0_5_6 + (-1/4 : K)*h_0_5_7 + (1/2 : K)*h_0_5_8 + -h_0_5_9 + h_0_6_10 + (2)*h_3_2_1 + (-5/4 : K)*h_3_2_2 + (-1/2 : K)*h_3_3_2 + -h_3_4_3 + (-1/2 : K)*h_3_5_5 + (-1/2 : K)*h_3_6_8 + h_3_0_0 + (5/4 : K)*h_3_2_0 + (5/4 : K)*h_3_3_1 + h_3_3_3 + (5/2 : K)*h_3_4_2 + (5/4 : K)*h_3_5_4 + (5/4 : K)*h_3_6_7 + h_3_6_9 + (-1/2 : K)*h_3_1_0 + h_3_1_1 + (-2)*h_3_1_2 + (-1/2 : K)*h_3_4_4 + h_3_4_5 + (-2)*h_3_4_6 + (-1/4 : K)*h_3_5_6 + (1/2 : K)*h_3_5_7 + -h_3_5_8 + (2)*h_3_5_9 + (-2)*h_3_6_10
  have hc4 : c.coeff 4=0 := by
    linear_combination (-5/4 : K)*h_0_2_2 + (-1/2 : K)*h_0_3_2 + -h_0_4_3 + (-1/2 : K)*h_0_5_5 + (-1/2 : K)*h_0_6_8 + -h_0_0_2 + (1/4 : K)*h_0_2_0 + (1/4 : K)*h_0_3_1 + -h_0_3_5 + (1/2 : K)*h_0_4_2 + (1/4 : K)*h_0_5_4 + (1/4 : K)*h_0_6_7 + (-1/2 : K)*h_0_1_0 + h_0_1_1 + (-2)*h_0_1_2 + (-1/2 : K)*h_0_4_4 + h_0_4_5 + (-2)*h_0_4_6 + (-1/4 : K)*h_0_5_6 + (1/2 : K)*h_0_5_7 + -h_0_5_8 + (2)*h_0_5_9 + (-2)*h_0_6_10 + h_3_0_1 + h_3_2_1 + (2)*h_3_2_2 + h_3_3_2 + h_3_3_4 + (2)*h_3_4_3 + h_3_5_5 + h_3_6_8
  have hc5 : c.coeff 5=0 := by
    linear_combination (1/4 : K)*h_0_0_1 + (1/4 : K)*h_0_2_1 + (-1/8 : K)*h_0_2_2 + (1/4 : K)*h_0_3_4 + (-1/2 : K)*h_0_0_2 + (1/8 : K)*h_0_2_0 + (1/8 : K)*h_0_3_1 + (-1/2 : K)*h_0_3_5 + (1/4 : K)*h_0_4_2 + (1/8 : K)*h_0_5_4 + (1/8 : K)*h_0_6_7 + (-1/4 : K)*h_0_1_0 + (1/2 : K)*h_0_1_1 + -h_0_1_2 + (-1/4 : K)*h_0_4_4 + (1/2 : K)*h_0_4_5 + -h_0_4_6 + (-1/8 : K)*h_0_5_6 + (1/4 : K)*h_0_5_7 + (-1/2 : K)*h_0_5_8 + h_0_5_9 + -h_0_6_10 + (5/4 : K)*h_3_2_2 + (1/2 : K)*h_3_3_2 + h_3_4_3 + (1/2 : K)*h_3_5_5 + (1/2 : K)*h_3_6_8 + h_3_0_2 + (-1/4 : K)*h_3_2_0 + (-1/4 : K)*h_3_3_1 + h_3_3_5 + (-1/2 : K)*h_3_4_2 + (-1/4 : K)*h_3_5_4 + (-1/4 : K)*h_3_6_7 + (1/2 : K)*h_3_1_0 + -h_3_1_1 + (2)*h_3_1_2 + (1/2 : K)*h_3_4_4 + -h_3_4_5 + (2)*h_3_4_6 + (1/4 : K)*h_3_5_6 + (-1/2 : K)*h_3_5_7 + h_3_5_8 + (-2)*h_3_5_9 + (2)*h_3_6_10
  have hc6 : c.coeff 6=0 := by
    linear_combination h_4_1_2 + h_4_4_6 + -h_4_5_9
  have hc7 : c.coeff 7=0 := by
    linear_combination h_6_0_0 + h_6_2_0 + (2)*h_6_2_1 + h_6_3_1 + h_6_3_3 + (2)*h_6_4_2 + h_6_5_4 + h_6_6_7
  have hc8 : c.coeff 8=0 := by
    linear_combination (-1/4 : K)*h_4_1_2 + (-1/4 : K)*h_4_4_6 + (1/4 : K)*h_4_5_9 + (1/4 : K)*h_5_0_0 + (-1/2 : K)*h_5_0_1 + h_5_0_2 + (1/2 : K)*h_5_1_0 + -h_5_1_1 + (1/4 : K)*h_5_2_2 + (1/4 : K)*h_5_3_3 + (-1/2 : K)*h_5_3_4 + h_5_3_5 + (1/2 : K)*h_5_4_4 + -h_5_4_5 + (1/4 : K)*h_5_5_6 + (-1/2 : K)*h_5_5_7 + h_5_5_8 + (1/2 : K)*h_6_0_0 + (1/2 : K)*h_6_2_0 + h_6_2_1 + (1/2 : K)*h_6_3_1 + (1/2 : K)*h_6_3_3 + h_6_4_2 + (1/2 : K)*h_6_5_4 + (1/2 : K)*h_6_6_7
  have hc9 : c.coeff 9=0 := by
    linear_combination -h_5_1_2 + -h_5_4_6 + h_5_5_9
  apply Polynomial.ext
  intro k
  by_cases hk : k≤9
  · interval_cases k <;> simp [hc0,hc1,hc2,hc3,hc4,hc5,hc6,hc7,hc8,hc9]
  · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hc (by omega)),coeff_zero]

set_option maxHeartbeats 1200000 in
theorem mixedOneThreeBase4_critical
    (E : Matrix (Fin 7) (Fin 10) K[X]) (c : K[X])
    (hE : ∀ i x, (E i x).natDegree ≤ (if i.val < 4 then 7 else 6))
    (hc : c.natDegree≤10)
    (hrel : E*mixedOneThreeBase4=(-c) • (1 : Matrix (Fin 7) (Fin 7) K[X]))
    (hsel0 : c.coeff 0=0)
    (hsel1 : c.coeff 1=0)
    : c=0 := by
  have hz0 (x : Fin 10) (k : ℕ) (hk : 7<k) : (E 0 x).coeff k=0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (by simpa using hE 0 x) hk)
  have hz1 (x : Fin 10) (k : ℕ) (hk : 7<k) : (E 1 x).coeff k=0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (by simpa using hE 1 x) hk)
  have hz2 (x : Fin 10) (k : ℕ) (hk : 7<k) : (E 2 x).coeff k=0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (by simpa using hE 2 x) hk)
  have hz3 (x : Fin 10) (k : ℕ) (hk : 7<k) : (E 3 x).coeff k=0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (by simpa using hE 3 x) hk)
  have hz4 (x : Fin 10) (k : ℕ) (hk : 6<k) : (E 4 x).coeff k=0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (by simpa using hE 4 x) hk)
  have hz5 (x : Fin 10) (k : ℕ) (hk : 6<k) : (E 5 x).coeff k=0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (by simpa using hE 5 x) hk)
  have hz6 (x : Fin 10) (k : ℕ) (hk : 6<k) : (E 6 x).coeff k=0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (by simpa using hE 6 x) hk)
  have h (i j : Fin 7) (k : ℕ) := scalar_relation_coeff E c hrel i j k
  have h_4_0_0 : -(E 4 3).coeff 0=0 := by
    have hh := h 4 0 0
    rw [if_neg (show (4 : Fin 7) ≠ 0 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_0_1 : -(E 4 3).coeff 1=0 := by
    have hh := h 4 0 1
    rw [if_neg (show (4 : Fin 7) ≠ 0 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_0_2 : -(E 4 3).coeff 2=0 := by
    have hh := h 4 0 2
    rw [if_neg (show (4 : Fin 7) ≠ 0 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_1_0 : -(E 4 4).coeff 0=0 := by
    have hh := h 4 1 0
    rw [if_neg (show (4 : Fin 7) ≠ 1 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_1_1 : -(E 4 4).coeff 1=0 := by
    have hh := h 4 1 1
    rw [if_neg (show (4 : Fin 7) ≠ 1 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_1_2 : -(E 4 4).coeff 2=0 := by
    have hh := h 4 1 2
    rw [if_neg (show (4 : Fin 7) ≠ 1 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_2_0 : -(E 4 5).coeff 0=0 := by
    have hh := h 4 2 0
    rw [if_neg (show (4 : Fin 7) ≠ 2 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_2_1 : -(E 4 5).coeff 1=0 := by
    have hh := h 4 2 1
    rw [if_neg (show (4 : Fin 7) ≠ 2 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_2_2 : -(E 4 5).coeff 2=0 := by
    have hh := h 4 2 2
    rw [if_neg (show (4 : Fin 7) ≠ 2 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_3_1 : -(E 4 6).coeff 1=0 := by
    have hh := h 4 3 1
    rw [if_neg (show (4 : Fin 7) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_3_2 : -(E 4 6).coeff 2=0 := by
    have hh := h 4 3 2
    rw [if_neg (show (4 : Fin 7) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_3_3 : (E 4 3).coeff 0 + -(E 4 6).coeff 3=0 := by
    have hh := h 4 3 3
    rw [if_neg (show (4 : Fin 7) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_3_4 : (E 4 3).coeff 1 + -(E 4 6).coeff 4=0 := by
    have hh := h 4 3 4
    rw [if_neg (show (4 : Fin 7) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_3_5 : (E 4 3).coeff 2 + -(E 4 6).coeff 5=0 := by
    have hh := h 4 3 5
    rw [if_neg (show (4 : Fin 7) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_4_2 : (E 4 5).coeff 1 + -(E 4 7).coeff 2 + c.coeff 2=0 := by
    have hh := h 4 4 2
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_4_3 : (E 4 5).coeff 2 + -(E 4 7).coeff 3 + c.coeff 3=0 := by
    have hh := h 4 4 3
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_4_4 : (E 4 4).coeff 0 + (E 4 5).coeff 3 + -(E 4 7).coeff 4 + c.coeff 4=0 := by
    have hh := h 4 4 4
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_4_5 : (E 4 4).coeff 1 + (E 4 5).coeff 4 + -(E 4 7).coeff 5 + c.coeff 5=0 := by
    have hh := h 4 4 5
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_4_6 : (E 4 4).coeff 2 + (E 4 5).coeff 5 + -(E 4 7).coeff 6 + c.coeff 6=0 := by
    have hh := h 4 4 6
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_5_4 : (E 4 5).coeff 0 + (E 4 6).coeff 1 + (2)*(E 4 7).coeff 2 + -(E 4 8).coeff 4=0 := by
    have hh := h 4 5 4
    rw [if_neg (show (4 : Fin 7) ≠ 5 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_5_5 : (E 4 5).coeff 1 + (E 4 6).coeff 2 + (2)*(E 4 7).coeff 3 + -(E 4 8).coeff 5=0 := by
    have hh := h 4 5 5
    rw [if_neg (show (4 : Fin 7) ≠ 5 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_5_6 : (E 4 5).coeff 2 + (E 4 6).coeff 3 + (2)*(E 4 7).coeff 4 + -(E 4 8).coeff 6=0 := by
    have hh := h 4 5 6
    rw [if_neg (show (4 : Fin 7) ≠ 5 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_5_7 : (E 4 5).coeff 3 + (E 4 6).coeff 4 + (2)*(E 4 7).coeff 5=0 := by
    have hh := h 4 5 7
    rw [if_neg (show (4 : Fin 7) ≠ 5 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_5_8 : (E 4 5).coeff 4 + (E 4 6).coeff 5 + (2)*(E 4 7).coeff 6=0 := by
    have hh := h 4 5 8
    rw [if_neg (show (4 : Fin 7) ≠ 5 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_5_9 : (E 4 5).coeff 5 + (E 4 6).coeff 6=0 := by
    have hh := h 4 5 9
    rw [if_neg (show (4 : Fin 7) ≠ 5 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_6_7 : (E 4 6).coeff 3 + -(E 4 8).coeff 6 + (E 4 8).coeff 4=0 := by
    have hh := h 4 6 7
    rw [if_neg (show (4 : Fin 7) ≠ 6 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_6_8 : (E 4 6).coeff 4 + (E 4 8).coeff 5=0 := by
    have hh := h 4 6 8
    rw [if_neg (show (4 : Fin 7) ≠ 6 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_6_9 : (E 4 6).coeff 5 + (E 4 8).coeff 6=0 := by
    have hh := h 4 6 9
    rw [if_neg (show (4 : Fin 7) ≠ 6 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_6_10 : (E 4 6).coeff 6=0 := by
    have hh := h 4 6 10
    rw [if_neg (show (4 : Fin 7) ≠ 6 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_0_0 : -(E 5 3).coeff 0=0 := by
    have hh := h 5 0 0
    rw [if_neg (show (5 : Fin 7) ≠ 0 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_0_1 : -(E 5 3).coeff 1=0 := by
    have hh := h 5 0 1
    rw [if_neg (show (5 : Fin 7) ≠ 0 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_0_2 : -(E 5 3).coeff 2=0 := by
    have hh := h 5 0 2
    rw [if_neg (show (5 : Fin 7) ≠ 0 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_1_0 : -(E 5 4).coeff 0=0 := by
    have hh := h 5 1 0
    rw [if_neg (show (5 : Fin 7) ≠ 1 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_1_1 : -(E 5 4).coeff 1=0 := by
    have hh := h 5 1 1
    rw [if_neg (show (5 : Fin 7) ≠ 1 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_1_2 : -(E 5 4).coeff 2=0 := by
    have hh := h 5 1 2
    rw [if_neg (show (5 : Fin 7) ≠ 1 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_2_0 : -(E 5 5).coeff 0=0 := by
    have hh := h 5 2 0
    rw [if_neg (show (5 : Fin 7) ≠ 2 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_2_1 : -(E 5 5).coeff 1=0 := by
    have hh := h 5 2 1
    rw [if_neg (show (5 : Fin 7) ≠ 2 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_2_2 : -(E 5 5).coeff 2=0 := by
    have hh := h 5 2 2
    rw [if_neg (show (5 : Fin 7) ≠ 2 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_3_1 : -(E 5 6).coeff 1=0 := by
    have hh := h 5 3 1
    rw [if_neg (show (5 : Fin 7) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_3_2 : -(E 5 6).coeff 2=0 := by
    have hh := h 5 3 2
    rw [if_neg (show (5 : Fin 7) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_3_3 : (E 5 3).coeff 0 + -(E 5 6).coeff 3=0 := by
    have hh := h 5 3 3
    rw [if_neg (show (5 : Fin 7) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_3_4 : (E 5 3).coeff 1 + -(E 5 6).coeff 4=0 := by
    have hh := h 5 3 4
    rw [if_neg (show (5 : Fin 7) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_3_5 : (E 5 3).coeff 2 + -(E 5 6).coeff 5=0 := by
    have hh := h 5 3 5
    rw [if_neg (show (5 : Fin 7) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_4_2 : (E 5 5).coeff 1 + -(E 5 7).coeff 2=0 := by
    have hh := h 5 4 2
    rw [if_neg (show (5 : Fin 7) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_4_3 : (E 5 5).coeff 2 + -(E 5 7).coeff 3=0 := by
    have hh := h 5 4 3
    rw [if_neg (show (5 : Fin 7) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_4_4 : (E 5 4).coeff 0 + (E 5 5).coeff 3 + -(E 5 7).coeff 4=0 := by
    have hh := h 5 4 4
    rw [if_neg (show (5 : Fin 7) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_4_5 : (E 5 4).coeff 1 + (E 5 5).coeff 4 + -(E 5 7).coeff 5=0 := by
    have hh := h 5 4 5
    rw [if_neg (show (5 : Fin 7) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_4_6 : (E 5 4).coeff 2 + (E 5 5).coeff 5 + -(E 5 7).coeff 6=0 := by
    have hh := h 5 4 6
    rw [if_neg (show (5 : Fin 7) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_5_4 : (E 5 5).coeff 0 + (E 5 6).coeff 1 + (2)*(E 5 7).coeff 2 + -(E 5 8).coeff 4 + c.coeff 4=0 := by
    have hh := h 5 5 4
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_5_5 : (E 5 5).coeff 1 + (E 5 6).coeff 2 + (2)*(E 5 7).coeff 3 + -(E 5 8).coeff 5 + c.coeff 5=0 := by
    have hh := h 5 5 5
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_5_6 : (E 5 5).coeff 2 + (E 5 6).coeff 3 + (2)*(E 5 7).coeff 4 + -(E 5 8).coeff 6 + c.coeff 6=0 := by
    have hh := h 5 5 6
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_5_7 : (E 5 5).coeff 3 + (E 5 6).coeff 4 + (2)*(E 5 7).coeff 5 + c.coeff 7=0 := by
    have hh := h 5 5 7
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_5_8 : (E 5 5).coeff 4 + (E 5 6).coeff 5 + (2)*(E 5 7).coeff 6 + c.coeff 8=0 := by
    have hh := h 5 5 8
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_5_9 : (E 5 5).coeff 5 + (E 5 6).coeff 6 + c.coeff 9=0 := by
    have hh := h 5 5 9
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_6_7 : (E 5 6).coeff 3 + -(E 5 8).coeff 6 + (E 5 8).coeff 4=0 := by
    have hh := h 5 6 7
    rw [if_neg (show (5 : Fin 7) ≠ 6 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_6_8 : (E 5 6).coeff 4 + (E 5 8).coeff 5=0 := by
    have hh := h 5 6 8
    rw [if_neg (show (5 : Fin 7) ≠ 6 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_6_9 : (E 5 6).coeff 5 + (E 5 8).coeff 6=0 := by
    have hh := h 5 6 9
    rw [if_neg (show (5 : Fin 7) ≠ 6 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_6_10 : (E 5 6).coeff 6=0 := by
    have hh := h 5 6 10
    rw [if_neg (show (5 : Fin 7) ≠ 6 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_6_0_0 : -(E 6 3).coeff 0=0 := by
    have hh := h 6 0 0
    rw [if_neg (show (6 : Fin 7) ≠ 0 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_6_0_1 : -(E 6 3).coeff 1=0 := by
    have hh := h 6 0 1
    rw [if_neg (show (6 : Fin 7) ≠ 0 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_6_0_2 : -(E 6 3).coeff 2=0 := by
    have hh := h 6 0 2
    rw [if_neg (show (6 : Fin 7) ≠ 0 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_6_1_0 : -(E 6 4).coeff 0=0 := by
    have hh := h 6 1 0
    rw [if_neg (show (6 : Fin 7) ≠ 1 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_6_1_1 : -(E 6 4).coeff 1=0 := by
    have hh := h 6 1 1
    rw [if_neg (show (6 : Fin 7) ≠ 1 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_6_1_2 : -(E 6 4).coeff 2=0 := by
    have hh := h 6 1 2
    rw [if_neg (show (6 : Fin 7) ≠ 1 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_6_2_0 : -(E 6 5).coeff 0=0 := by
    have hh := h 6 2 0
    rw [if_neg (show (6 : Fin 7) ≠ 2 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_6_2_1 : -(E 6 5).coeff 1=0 := by
    have hh := h 6 2 1
    rw [if_neg (show (6 : Fin 7) ≠ 2 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_6_2_2 : -(E 6 5).coeff 2=0 := by
    have hh := h 6 2 2
    rw [if_neg (show (6 : Fin 7) ≠ 2 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_6_3_1 : -(E 6 6).coeff 1=0 := by
    have hh := h 6 3 1
    rw [if_neg (show (6 : Fin 7) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_6_3_2 : -(E 6 6).coeff 2=0 := by
    have hh := h 6 3 2
    rw [if_neg (show (6 : Fin 7) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_6_3_3 : (E 6 3).coeff 0 + -(E 6 6).coeff 3=0 := by
    have hh := h 6 3 3
    rw [if_neg (show (6 : Fin 7) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_6_3_4 : (E 6 3).coeff 1 + -(E 6 6).coeff 4=0 := by
    have hh := h 6 3 4
    rw [if_neg (show (6 : Fin 7) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_6_3_5 : (E 6 3).coeff 2 + -(E 6 6).coeff 5=0 := by
    have hh := h 6 3 5
    rw [if_neg (show (6 : Fin 7) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_6_4_2 : (E 6 5).coeff 1 + -(E 6 7).coeff 2=0 := by
    have hh := h 6 4 2
    rw [if_neg (show (6 : Fin 7) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_6_4_3 : (E 6 5).coeff 2 + -(E 6 7).coeff 3=0 := by
    have hh := h 6 4 3
    rw [if_neg (show (6 : Fin 7) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_6_4_4 : (E 6 4).coeff 0 + (E 6 5).coeff 3 + -(E 6 7).coeff 4=0 := by
    have hh := h 6 4 4
    rw [if_neg (show (6 : Fin 7) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_6_4_5 : (E 6 4).coeff 1 + (E 6 5).coeff 4 + -(E 6 7).coeff 5=0 := by
    have hh := h 6 4 5
    rw [if_neg (show (6 : Fin 7) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_6_4_6 : (E 6 4).coeff 2 + (E 6 5).coeff 5 + -(E 6 7).coeff 6=0 := by
    have hh := h 6 4 6
    rw [if_neg (show (6 : Fin 7) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_6_5_4 : (E 6 5).coeff 0 + (E 6 6).coeff 1 + (2)*(E 6 7).coeff 2 + -(E 6 8).coeff 4=0 := by
    have hh := h 6 5 4
    rw [if_neg (show (6 : Fin 7) ≠ 5 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_6_5_5 : (E 6 5).coeff 1 + (E 6 6).coeff 2 + (2)*(E 6 7).coeff 3 + -(E 6 8).coeff 5=0 := by
    have hh := h 6 5 5
    rw [if_neg (show (6 : Fin 7) ≠ 5 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_6_5_6 : (E 6 5).coeff 2 + (E 6 6).coeff 3 + (2)*(E 6 7).coeff 4 + -(E 6 8).coeff 6=0 := by
    have hh := h 6 5 6
    rw [if_neg (show (6 : Fin 7) ≠ 5 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_6_5_7 : (E 6 5).coeff 3 + (E 6 6).coeff 4 + (2)*(E 6 7).coeff 5=0 := by
    have hh := h 6 5 7
    rw [if_neg (show (6 : Fin 7) ≠ 5 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_6_5_8 : (E 6 5).coeff 4 + (E 6 6).coeff 5 + (2)*(E 6 7).coeff 6=0 := by
    have hh := h 6 5 8
    rw [if_neg (show (6 : Fin 7) ≠ 5 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_6_5_9 : (E 6 5).coeff 5 + (E 6 6).coeff 6=0 := by
    have hh := h 6 5 9
    rw [if_neg (show (6 : Fin 7) ≠ 5 by decide)] at hh
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_6_6_7 : (E 6 6).coeff 3 + -(E 6 8).coeff 6 + (E 6 8).coeff 4 + c.coeff 7=0 := by
    have hh := h 6 6 7
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_6_6_8 : (E 6 6).coeff 4 + (E 6 8).coeff 5 + c.coeff 8=0 := by
    have hh := h 6 6 8
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_6_6_9 : (E 6 6).coeff 5 + (E 6 8).coeff 6 + c.coeff 9=0 := by
    have hh := h 6 6 9
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_6_6_10 : (E 6 6).coeff 6 + c.coeff 10=0 := by
    have hh := h 6 6 10
    norm_num [mixedOneThreeBase4,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5,hz6] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have hc0 : c.coeff 0=0 := by
    linear_combination hsel0
  have hc1 : c.coeff 1=0 := by
    linear_combination hsel1
  have hc2 : c.coeff 2=0 := by
    linear_combination h_4_2_1 + (1/2 : K)*h_4_0_0 + (1/2 : K)*h_4_0_2 + (1/2 : K)*h_4_2_0 + (1/2 : K)*h_4_3_1 + (1/2 : K)*h_4_3_3 + (1/2 : K)*h_4_3_5 + h_4_4_2 + (1/2 : K)*h_4_5_4 + (1/2 : K)*h_4_6_7 + (1/2 : K)*h_4_6_9
  have hc3 : c.coeff 3=0 := by
    linear_combination (1/2 : K)*h_4_0_1 + (1/2 : K)*h_4_2_1 + h_4_2_2 + (1/2 : K)*h_4_3_2 + (1/2 : K)*h_4_3_4 + h_4_4_3 + (1/2 : K)*h_4_5_5 + (1/2 : K)*h_4_6_8
  have hc4 : c.coeff 4=0 := by
    linear_combination (2)*h_5_2_1 + h_5_0_0 + h_5_0_2 + h_5_2_0 + h_5_3_1 + h_5_3_3 + h_5_3_5 + (2)*h_5_4_2 + h_5_5_4 + h_5_6_7 + h_5_6_9
  have hc5 : c.coeff 5=0 := by
    linear_combination h_5_0_1 + h_5_2_1 + (2)*h_5_2_2 + h_5_3_2 + h_5_3_4 + (2)*h_5_4_3 + h_5_5_5 + h_5_6_8
  have hc6 : c.coeff 6=0 := by
    linear_combination (-1/4 : K)*h_4_0_1 + (1/8 : K)*h_4_2_2 + (-1/4 : K)*h_4_3_4 + (1/8 : K)*h_4_0_0 + (5/8 : K)*h_4_0_2 + (1/8 : K)*h_4_3_3 + (5/8 : K)*h_4_3_5 + (1/8 : K)*h_4_6_9 + (1/4 : K)*h_4_1_0 + (-1/2 : K)*h_4_1_1 + h_4_1_2 + (1/4 : K)*h_4_4_4 + (-1/2 : K)*h_4_4_5 + h_4_4_6 + (1/8 : K)*h_4_5_6 + (-1/4 : K)*h_4_5_7 + (1/2 : K)*h_4_5_8 + -h_4_5_9 + h_4_6_10 + (1/2 : K)*h_5_0_1 + h_5_2_2 + (1/2 : K)*h_5_3_2 + (1/2 : K)*h_5_3_4 + h_5_4_3 + (1/2 : K)*h_5_5_5 + (1/2 : K)*h_5_6_8 + (-1/4 : K)*h_5_0_0 + (-1/4 : K)*h_5_0_2 + (-1/4 : K)*h_5_2_0 + (-1/4 : K)*h_5_3_1 + (-1/4 : K)*h_5_3_3 + (-1/4 : K)*h_5_3_5 + (-1/2 : K)*h_5_4_2 + (-1/4 : K)*h_5_5_4 + (-1/4 : K)*h_5_6_7 + (-1/4 : K)*h_5_6_9
  have hc7 : c.coeff 7=0 := by
    linear_combination (1/24 : K)*h_4_0_1 + (-1/48 : K)*h_4_2_2 + (1/24 : K)*h_4_3_4 + (-1/48 : K)*h_4_0_0 + (-5/48 : K)*h_4_0_2 + (-1/48 : K)*h_4_3_3 + (-5/48 : K)*h_4_3_5 + (-1/48 : K)*h_4_6_9 + (-1/24 : K)*h_4_1_0 + (1/12 : K)*h_4_1_1 + (-1/6 : K)*h_4_1_2 + (-1/24 : K)*h_4_4_4 + (1/12 : K)*h_4_4_5 + (-1/6 : K)*h_4_4_6 + (-1/48 : K)*h_4_5_6 + (1/24 : K)*h_4_5_7 + (-1/12 : K)*h_4_5_8 + (1/6 : K)*h_4_5_9 + (-1/6 : K)*h_4_6_10 + (-5/12 : K)*h_5_0_1 + (-1/12 : K)*h_5_3_2 + (-5/12 : K)*h_5_3_4 + (-1/6 : K)*h_5_4_3 + (-1/12 : K)*h_5_5_5 + (-1/12 : K)*h_5_6_8 + (5/24 : K)*h_5_0_0 + (7/8 : K)*h_5_0_2 + (1/24 : K)*h_5_2_0 + (1/24 : K)*h_5_3_1 + (5/24 : K)*h_5_3_3 + (7/8 : K)*h_5_3_5 + (1/12 : K)*h_5_4_2 + (1/24 : K)*h_5_5_4 + (1/24 : K)*h_5_6_7 + (5/24 : K)*h_5_6_9 + (1/3 : K)*h_5_1_0 + (-2/3 : K)*h_5_1_1 + (4/3 : K)*h_5_1_2 + (1/3 : K)*h_5_4_4 + (-2/3 : K)*h_5_4_5 + (4/3 : K)*h_5_4_6 + (1/6 : K)*h_5_5_6 + (-1/3 : K)*h_5_5_7 + (2/3 : K)*h_5_5_8 + (-4/3 : K)*h_5_5_9 + (4/3 : K)*h_5_6_10 + (-2/3 : K)*h_6_0_1 + (2)*h_6_2_1 + (-4/3 : K)*h_6_2_2 + (-2/3 : K)*h_6_3_2 + (-2/3 : K)*h_6_3_4 + (-4/3 : K)*h_6_4_3 + (-2/3 : K)*h_6_5_5 + (-2/3 : K)*h_6_6_8 + (4/3 : K)*h_6_0_0 + (4/3 : K)*h_6_0_2 + (4/3 : K)*h_6_2_0 + (4/3 : K)*h_6_3_1 + (4/3 : K)*h_6_3_3 + (4/3 : K)*h_6_3_5 + (8/3 : K)*h_6_4_2 + (4/3 : K)*h_6_5_4 + (4/3 : K)*h_6_6_7 + (4/3 : K)*h_6_6_9
  have hc8 : c.coeff 8=0 := by
    linear_combination h_6_0_1 + h_6_2_1 + (2)*h_6_2_2 + h_6_3_2 + h_6_3_4 + (2)*h_6_4_3 + h_6_5_5 + h_6_6_8
  have hc9 : c.coeff 9=0 := by
    linear_combination (-1/24 : K)*h_4_0_1 + (1/48 : K)*h_4_2_2 + (-1/24 : K)*h_4_3_4 + (1/48 : K)*h_4_0_0 + (5/48 : K)*h_4_0_2 + (1/48 : K)*h_4_3_3 + (5/48 : K)*h_4_3_5 + (1/48 : K)*h_4_6_9 + (1/24 : K)*h_4_1_0 + (-1/12 : K)*h_4_1_1 + (1/6 : K)*h_4_1_2 + (1/24 : K)*h_4_4_4 + (-1/12 : K)*h_4_4_5 + (1/6 : K)*h_4_4_6 + (1/48 : K)*h_4_5_6 + (-1/24 : K)*h_4_5_7 + (1/12 : K)*h_4_5_8 + (-1/6 : K)*h_4_5_9 + (1/6 : K)*h_4_6_10 + (5/12 : K)*h_5_0_1 + (1/12 : K)*h_5_3_2 + (5/12 : K)*h_5_3_4 + (1/6 : K)*h_5_4_3 + (1/12 : K)*h_5_5_5 + (1/12 : K)*h_5_6_8 + (-5/24 : K)*h_5_0_0 + (-7/8 : K)*h_5_0_2 + (-1/24 : K)*h_5_2_0 + (-1/24 : K)*h_5_3_1 + (-5/24 : K)*h_5_3_3 + (-7/8 : K)*h_5_3_5 + (-1/12 : K)*h_5_4_2 + (-1/24 : K)*h_5_5_4 + (-1/24 : K)*h_5_6_7 + (-5/24 : K)*h_5_6_9 + (-1/3 : K)*h_5_1_0 + (2/3 : K)*h_5_1_1 + (-4/3 : K)*h_5_1_2 + (-1/3 : K)*h_5_4_4 + (2/3 : K)*h_5_4_5 + (-4/3 : K)*h_5_4_6 + (-1/6 : K)*h_5_5_6 + (1/3 : K)*h_5_5_7 + (-2/3 : K)*h_5_5_8 + (4/3 : K)*h_5_5_9 + (-4/3 : K)*h_5_6_10 + (2/3 : K)*h_6_0_1 + (4/3 : K)*h_6_2_2 + (2/3 : K)*h_6_3_2 + (2/3 : K)*h_6_3_4 + (4/3 : K)*h_6_4_3 + (2/3 : K)*h_6_5_5 + (2/3 : K)*h_6_6_8 + (-1/3 : K)*h_6_0_0 + (-1/3 : K)*h_6_0_2 + (-1/3 : K)*h_6_2_0 + (-1/3 : K)*h_6_3_1 + (-1/3 : K)*h_6_3_3 + (-1/3 : K)*h_6_3_5 + (-2/3 : K)*h_6_4_2 + (-1/3 : K)*h_6_5_4 + (-1/3 : K)*h_6_6_7 + (-1/3 : K)*h_6_6_9
  have hc10 : c.coeff 10=0 := by
    linear_combination (1/192 : K)*h_4_0_1 + (-1/384 : K)*h_4_2_2 + (1/192 : K)*h_4_3_4 + (-1/384 : K)*h_4_0_0 + (-5/384 : K)*h_4_0_2 + (-1/384 : K)*h_4_3_3 + (-5/384 : K)*h_4_3_5 + (-1/384 : K)*h_4_6_9 + (-1/192 : K)*h_4_1_0 + (1/96 : K)*h_4_1_1 + (-1/48 : K)*h_4_1_2 + (-1/192 : K)*h_4_4_4 + (1/96 : K)*h_4_4_5 + (-1/48 : K)*h_4_4_6 + (-1/384 : K)*h_4_5_6 + (1/192 : K)*h_4_5_7 + (-1/96 : K)*h_4_5_8 + (1/48 : K)*h_4_5_9 + (-1/48 : K)*h_4_6_10 + (-5/96 : K)*h_5_0_1 + (-1/96 : K)*h_5_3_2 + (-5/96 : K)*h_5_3_4 + (-1/48 : K)*h_5_4_3 + (-1/96 : K)*h_5_5_5 + (-1/96 : K)*h_5_6_8 + (5/192 : K)*h_5_0_0 + (7/64 : K)*h_5_0_2 + (1/192 : K)*h_5_2_0 + (1/192 : K)*h_5_3_1 + (5/192 : K)*h_5_3_3 + (7/64 : K)*h_5_3_5 + (1/96 : K)*h_5_4_2 + (1/192 : K)*h_5_5_4 + (1/192 : K)*h_5_6_7 + (5/192 : K)*h_5_6_9 + (1/24 : K)*h_5_1_0 + (-1/12 : K)*h_5_1_1 + (1/6 : K)*h_5_1_2 + (1/24 : K)*h_5_4_4 + (-1/12 : K)*h_5_4_5 + (1/6 : K)*h_5_4_6 + (1/48 : K)*h_5_5_6 + (-1/24 : K)*h_5_5_7 + (1/12 : K)*h_5_5_8 + (-1/6 : K)*h_5_5_9 + (1/6 : K)*h_5_6_10 + (-1/3 : K)*h_6_0_1 + (-1/24 : K)*h_6_2_2 + (-1/12 : K)*h_6_3_2 + (-1/3 : K)*h_6_3_4 + (-1/6 : K)*h_6_4_3 + (-1/12 : K)*h_6_5_5 + (-1/12 : K)*h_6_6_8 + (1/6 : K)*h_6_0_0 + (2/3 : K)*h_6_0_2 + (1/24 : K)*h_6_2_0 + (1/24 : K)*h_6_3_1 + (1/6 : K)*h_6_3_3 + (2/3 : K)*h_6_3_5 + (1/12 : K)*h_6_4_2 + (1/24 : K)*h_6_5_4 + (1/24 : K)*h_6_6_7 + (1/6 : K)*h_6_6_9 + (1/4 : K)*h_6_1_0 + (-1/2 : K)*h_6_1_1 + h_6_1_2 + (1/4 : K)*h_6_4_4 + (-1/2 : K)*h_6_4_5 + h_6_4_6 + (1/8 : K)*h_6_5_6 + (-1/4 : K)*h_6_5_7 + (1/2 : K)*h_6_5_8 + -h_6_5_9 + h_6_6_10
  apply Polynomial.ext
  intro k
  by_cases hk : k≤10
  · interval_cases k <;> simp [hc0,hc1,hc2,hc3,hc4,hc5,hc6,hc7,hc8,hc9,hc10]
  · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hc (by omega)),coeff_zero]

end FD56
