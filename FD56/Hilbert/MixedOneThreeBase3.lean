/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.CubicScalarInduction
import FD56.Hilbert.FiniteMatrixEvaluation
import Mathlib.Tactic.LinearCombination

/-! Exact scalar obstruction identities for the three-high-column base with 3 low columns. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option maxRecDepth 4096

variable {K : Type*} [Field K] [CharZero K]

def mixedOneThreeBase3 : Matrix (Fin 9) (Fin 6) K[X] :=
  ![![X^3,0,0,0,0,0],
    ![0,X^3,0,0,0,0],
    ![0,0,X^3,0,0,0],
    ![-1,0,0,X^4,0,0],
    ![0,-1,0,X^2+X^2,X^4,0],
    ![0,0,-1,X^3,X^2,X^4],
    ![0,0,0,-1,-X+X^2,X^2+X^2],
    ![0,0,0,0,-1,X^3],
    ![0,0,0,0,0,-1]]

omit [CharZero K] in
private theorem scalar_relation_coeff
    (E : Matrix (Fin 6) (Fin 9) K[X]) (c : K[X])
    (hrel : E*mixedOneThreeBase3=(-c) • (1 : Matrix (Fin 6) (Fin 6) K[X]))
    (i j : Fin 6) (k : ℕ) :
    ((E*mixedOneThreeBase3 (K := K)) i j).coeff k+(if i=j then c.coeff k else 0)=0 := by
  have h := congrArg (fun Z : Matrix (Fin 6) (Fin 6) K[X] => (Z i j).coeff k) hrel
  by_cases hij : i=j
  · simp [Matrix.smul_apply,Matrix.one_apply,hij] at h ⊢
    exact add_eq_zero_iff_eq_neg.mpr h
  · simpa [Matrix.smul_apply,Matrix.one_apply,hij] using h

set_option maxHeartbeats 1200000 in
theorem mixedOneThreeBase3_zero
    (E : Matrix (Fin 6) (Fin 9) K[X]) (c : K[X])
    (hE : ∀ i x, (E i x).natDegree ≤ (if i.val < 3 then 5 else 4))
    (hc : c.natDegree≤8)
    (hrel : E*mixedOneThreeBase3=(-c) • (1 : Matrix (Fin 6) (Fin 6) K[X]))
    : c=0 := by
  have hz0 (x : Fin 9) (k : ℕ) (hk : 5<k) : (E 0 x).coeff k=0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (by simpa using hE 0 x) hk)
  have hz1 (x : Fin 9) (k : ℕ) (hk : 5<k) : (E 1 x).coeff k=0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (by simpa using hE 1 x) hk)
  have hz2 (x : Fin 9) (k : ℕ) (hk : 5<k) : (E 2 x).coeff k=0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (by simpa using hE 2 x) hk)
  have hz3 (x : Fin 9) (k : ℕ) (hk : 4<k) : (E 3 x).coeff k=0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (by simpa using hE 3 x) hk)
  have hz4 (x : Fin 9) (k : ℕ) (hk : 4<k) : (E 4 x).coeff k=0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (by simpa using hE 4 x) hk)
  have hz5 (x : Fin 9) (k : ℕ) (hk : 4<k) : (E 5 x).coeff k=0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (by simpa using hE 5 x) hk)
  have h (i j : Fin 6) (k : ℕ) := scalar_relation_coeff E c hrel i j k
  have h_0_0_0 : -(E 0 3).coeff 0 + c.coeff 0=0 := by
    have hh := h 0 0 0
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_0_1 : -(E 0 3).coeff 1 + c.coeff 1=0 := by
    have hh := h 0 0 1
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_0_2 : -(E 0 3).coeff 2 + c.coeff 2=0 := by
    have hh := h 0 0 2
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_1_0 : -(E 0 4).coeff 0=0 := by
    have hh := h 0 1 0
    rw [if_neg (show (0 : Fin 6) ≠ 1 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_1_1 : -(E 0 4).coeff 1=0 := by
    have hh := h 0 1 1
    rw [if_neg (show (0 : Fin 6) ≠ 1 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_1_2 : -(E 0 4).coeff 2=0 := by
    have hh := h 0 1 2
    rw [if_neg (show (0 : Fin 6) ≠ 1 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_2_0 : -(E 0 5).coeff 0=0 := by
    have hh := h 0 2 0
    rw [if_neg (show (0 : Fin 6) ≠ 2 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_2_1 : -(E 0 5).coeff 1=0 := by
    have hh := h 0 2 1
    rw [if_neg (show (0 : Fin 6) ≠ 2 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_2_2 : -(E 0 5).coeff 2=0 := by
    have hh := h 0 2 2
    rw [if_neg (show (0 : Fin 6) ≠ 2 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_3_1 : -(E 0 6).coeff 1=0 := by
    have hh := h 0 3 1
    rw [if_neg (show (0 : Fin 6) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_3_2 : (2)*(E 0 4).coeff 0 + -(E 0 6).coeff 2=0 := by
    have hh := h 0 3 2
    rw [if_neg (show (0 : Fin 6) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_3_3 : (2)*(E 0 4).coeff 1 + (E 0 5).coeff 0 + -(E 0 6).coeff 3=0 := by
    have hh := h 0 3 3
    rw [if_neg (show (0 : Fin 6) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_3_4 : (E 0 3).coeff 0 + (2)*(E 0 4).coeff 2 + (E 0 5).coeff 1 + -(E 0 6).coeff 4=0 := by
    have hh := h 0 3 4
    rw [if_neg (show (0 : Fin 6) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_3_5 : (E 0 3).coeff 1 + (2)*(E 0 4).coeff 3 + (E 0 5).coeff 2 + -(E 0 6).coeff 5=0 := by
    have hh := h 0 3 5
    rw [if_neg (show (0 : Fin 6) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_3_6 : (E 0 3).coeff 2 + (2)*(E 0 4).coeff 4 + (E 0 5).coeff 3=0 := by
    have hh := h 0 3 6
    rw [if_neg (show (0 : Fin 6) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_4_3 : (E 0 5).coeff 1 + -(E 0 6).coeff 2 + (E 0 6).coeff 1 + -(E 0 7).coeff 3=0 := by
    have hh := h 0 4 3
    rw [if_neg (show (0 : Fin 6) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_4_4 : (E 0 4).coeff 0 + (E 0 5).coeff 2 + -(E 0 6).coeff 3 + (E 0 6).coeff 2 + -(E 0 7).coeff 4=0 := by
    have hh := h 0 4 4
    rw [if_neg (show (0 : Fin 6) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_4_5 : (E 0 4).coeff 1 + (E 0 5).coeff 3 + -(E 0 6).coeff 4 + (E 0 6).coeff 3 + -(E 0 7).coeff 5=0 := by
    have hh := h 0 4 5
    rw [if_neg (show (0 : Fin 6) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_4_6 : (E 0 4).coeff 2 + (E 0 5).coeff 4 + -(E 0 6).coeff 5 + (E 0 6).coeff 4=0 := by
    have hh := h 0 4 6
    rw [if_neg (show (0 : Fin 6) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_4_7 : (E 0 4).coeff 3 + (E 0 5).coeff 5 + (E 0 6).coeff 5=0 := by
    have hh := h 0 4 7
    rw [if_neg (show (0 : Fin 6) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_4_8 : (E 0 4).coeff 4=0 := by
    have hh := h 0 4 8
    rw [if_neg (show (0 : Fin 6) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_5_6 : (E 0 5).coeff 2 + (2)*(E 0 6).coeff 4 + (E 0 7).coeff 3=0 := by
    have hh := h 0 5 6
    rw [if_neg (show (0 : Fin 6) ≠ 5 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_5_7 : (E 0 5).coeff 3 + (2)*(E 0 6).coeff 5 + (E 0 7).coeff 4=0 := by
    have hh := h 0 5 7
    rw [if_neg (show (0 : Fin 6) ≠ 5 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_5_8 : (E 0 5).coeff 4 + (E 0 7).coeff 5=0 := by
    have hh := h 0 5 8
    rw [if_neg (show (0 : Fin 6) ≠ 5 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_0_5_9 : (E 0 5).coeff 5=0 := by
    have hh := h 0 5 9
    rw [if_neg (show (0 : Fin 6) ≠ 5 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_0_0 : -(E 3 3).coeff 0=0 := by
    have hh := h 3 0 0
    rw [if_neg (show (3 : Fin 6) ≠ 0 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_0_1 : -(E 3 3).coeff 1=0 := by
    have hh := h 3 0 1
    rw [if_neg (show (3 : Fin 6) ≠ 0 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_0_2 : -(E 3 3).coeff 2=0 := by
    have hh := h 3 0 2
    rw [if_neg (show (3 : Fin 6) ≠ 0 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_1_0 : -(E 3 4).coeff 0=0 := by
    have hh := h 3 1 0
    rw [if_neg (show (3 : Fin 6) ≠ 1 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_1_1 : -(E 3 4).coeff 1=0 := by
    have hh := h 3 1 1
    rw [if_neg (show (3 : Fin 6) ≠ 1 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_1_2 : -(E 3 4).coeff 2=0 := by
    have hh := h 3 1 2
    rw [if_neg (show (3 : Fin 6) ≠ 1 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_2_0 : -(E 3 5).coeff 0=0 := by
    have hh := h 3 2 0
    rw [if_neg (show (3 : Fin 6) ≠ 2 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_2_1 : -(E 3 5).coeff 1=0 := by
    have hh := h 3 2 1
    rw [if_neg (show (3 : Fin 6) ≠ 2 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_2_2 : -(E 3 5).coeff 2=0 := by
    have hh := h 3 2 2
    rw [if_neg (show (3 : Fin 6) ≠ 2 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_3_0 : -(E 3 6).coeff 0 + c.coeff 0=0 := by
    have hh := h 3 3 0
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_3_1 : -(E 3 6).coeff 1 + c.coeff 1=0 := by
    have hh := h 3 3 1
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_3_2 : (2)*(E 3 4).coeff 0 + -(E 3 6).coeff 2 + c.coeff 2=0 := by
    have hh := h 3 3 2
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_3_3 : (2)*(E 3 4).coeff 1 + (E 3 5).coeff 0 + -(E 3 6).coeff 3 + c.coeff 3=0 := by
    have hh := h 3 3 3
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_3_4 : (E 3 3).coeff 0 + (2)*(E 3 4).coeff 2 + (E 3 5).coeff 1 + -(E 3 6).coeff 4 + c.coeff 4=0 := by
    have hh := h 3 3 4
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_3_5 : (E 3 3).coeff 1 + (2)*(E 3 4).coeff 3 + (E 3 5).coeff 2 + c.coeff 5=0 := by
    have hh := h 3 3 5
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_3_6 : (E 3 3).coeff 2 + (2)*(E 3 4).coeff 4 + (E 3 5).coeff 3 + c.coeff 6=0 := by
    have hh := h 3 3 6
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_4_2 : (E 3 5).coeff 0 + -(E 3 6).coeff 1 + (E 3 6).coeff 0 + -(E 3 7).coeff 2=0 := by
    have hh := h 3 4 2
    rw [if_neg (show (3 : Fin 6) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_4_3 : (E 3 5).coeff 1 + -(E 3 6).coeff 2 + (E 3 6).coeff 1 + -(E 3 7).coeff 3=0 := by
    have hh := h 3 4 3
    rw [if_neg (show (3 : Fin 6) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_4_5 : (E 3 4).coeff 1 + (E 3 5).coeff 3 + -(E 3 6).coeff 4 + (E 3 6).coeff 3=0 := by
    have hh := h 3 4 5
    rw [if_neg (show (3 : Fin 6) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_4_7 : (E 3 4).coeff 3=0 := by
    have hh := h 3 4 7
    rw [if_neg (show (3 : Fin 6) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_4_8 : (E 3 4).coeff 4=0 := by
    have hh := h 3 4 8
    rw [if_neg (show (3 : Fin 6) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_5_5 : (E 3 5).coeff 1 + (2)*(E 3 6).coeff 3 + (E 3 7).coeff 2=0 := by
    have hh := h 3 5 5
    rw [if_neg (show (3 : Fin 6) ≠ 5 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_5_6 : (E 3 5).coeff 2 + (2)*(E 3 6).coeff 4 + (E 3 7).coeff 3=0 := by
    have hh := h 3 5 6
    rw [if_neg (show (3 : Fin 6) ≠ 5 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_0_0 : -(E 4 3).coeff 0=0 := by
    have hh := h 4 0 0
    rw [if_neg (show (4 : Fin 6) ≠ 0 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_0_1 : -(E 4 3).coeff 1=0 := by
    have hh := h 4 0 1
    rw [if_neg (show (4 : Fin 6) ≠ 0 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_0_2 : -(E 4 3).coeff 2=0 := by
    have hh := h 4 0 2
    rw [if_neg (show (4 : Fin 6) ≠ 0 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_1_1 : -(E 4 4).coeff 1=0 := by
    have hh := h 4 1 1
    rw [if_neg (show (4 : Fin 6) ≠ 1 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_1_2 : -(E 4 4).coeff 2=0 := by
    have hh := h 4 1 2
    rw [if_neg (show (4 : Fin 6) ≠ 1 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_2_0 : -(E 4 5).coeff 0=0 := by
    have hh := h 4 2 0
    rw [if_neg (show (4 : Fin 6) ≠ 2 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_2_1 : -(E 4 5).coeff 1=0 := by
    have hh := h 4 2 1
    rw [if_neg (show (4 : Fin 6) ≠ 2 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_2_2 : -(E 4 5).coeff 2=0 := by
    have hh := h 4 2 2
    rw [if_neg (show (4 : Fin 6) ≠ 2 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_3_3 : (2)*(E 4 4).coeff 1 + (E 4 5).coeff 0 + -(E 4 6).coeff 3=0 := by
    have hh := h 4 3 3
    rw [if_neg (show (4 : Fin 6) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_3_4 : (E 4 3).coeff 0 + (2)*(E 4 4).coeff 2 + (E 4 5).coeff 1 + -(E 4 6).coeff 4=0 := by
    have hh := h 4 3 4
    rw [if_neg (show (4 : Fin 6) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_3_5 : (E 4 3).coeff 1 + (2)*(E 4 4).coeff 3 + (E 4 5).coeff 2=0 := by
    have hh := h 4 3 5
    rw [if_neg (show (4 : Fin 6) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_3_6 : (E 4 3).coeff 2 + (2)*(E 4 4).coeff 4 + (E 4 5).coeff 3=0 := by
    have hh := h 4 3 6
    rw [if_neg (show (4 : Fin 6) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_4_5 : (E 4 4).coeff 1 + (E 4 5).coeff 3 + -(E 4 6).coeff 4 + (E 4 6).coeff 3 + c.coeff 5=0 := by
    have hh := h 4 4 5
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_4_7 : (E 4 4).coeff 3 + c.coeff 7=0 := by
    have hh := h 4 4 7
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_4_8 : (E 4 4).coeff 4 + c.coeff 8=0 := by
    have hh := h 4 4 8
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have hc0 : c.coeff 0=0 := by
    linear_combination h_0_0_0 + -h_0_1_0 + (2)*h_0_1_2 + (3/2 : K)*h_0_2_1 + (1/2 : K)*h_0_2_2 + (1/2 : K)*h_0_3_1 + (-1/2 : K)*h_0_3_2 + h_0_3_4 + (1/2 : K)*h_0_4_3 + (1/2 : K)*h_0_5_6
  have hc1 : c.coeff 1=0 := by
    linear_combination (15)*h_0_1_0 + (3)*h_0_1_2 + (-3)*h_0_2_1 + h_0_2_2 + (-3)*h_0_3_1 + (6)*h_0_3_2 + (-3)*h_0_4_3 + (-3)*h_0_5_6 + (-15)*h_0_1_1 + (-6)*h_0_2_0 + (-6)*h_0_3_3 + (3)*h_0_4_4 + (-3)*h_0_4_5 + (3)*h_0_4_6 + (3)*h_0_5_7 + (-3)*h_0_5_8 + h_0_0_1 + h_0_3_5 + (-2)*h_0_4_7 + (2)*h_0_5_9
  have hc2 : c.coeff 2=0 := by
    linear_combination (7)*h_0_1_0 + (2)*h_0_1_2 + (-2)*h_0_2_1 + -h_0_2_2 + (-2)*h_0_3_1 + (3)*h_0_3_2 + (-2)*h_0_4_3 + (-2)*h_0_5_6 + h_0_0_2 + (-8)*h_0_1_1 + (-3)*h_0_2_0 + (-3)*h_0_3_3 + h_0_3_6 + h_0_4_4 + (-2)*h_0_4_5 + (2)*h_0_4_6 + (-2)*h_0_4_8 + h_0_5_7 + (-2)*h_0_5_8
  have hc3 : c.coeff 3=0 := by
    linear_combination (-1/2 : K)*h_0_0_0 + (8)*h_0_1_0 + (1/2 : K)*h_0_1_2 + (-9/4 : K)*h_0_2_1 + (1/4 : K)*h_0_2_2 + (-7/4 : K)*h_0_3_1 + (13/4 : K)*h_0_3_2 + (-1/2 : K)*h_0_3_4 + (-7/4 : K)*h_0_4_3 + (-7/4 : K)*h_0_5_6 + (-15/2 : K)*h_0_1_1 + (-3)*h_0_2_0 + (-3)*h_0_3_3 + (3/2 : K)*h_0_4_4 + (-3/2 : K)*h_0_4_5 + (3/2 : K)*h_0_4_6 + (3/2 : K)*h_0_5_7 + (-3/2 : K)*h_0_5_8 + (1/2 : K)*h_0_0_1 + (1/2 : K)*h_0_3_5 + -h_0_4_7 + h_0_5_9 + (2)*h_3_1_1 + (3/2 : K)*h_3_2_0 + (1/2 : K)*h_3_2_1 + h_3_3_3 + (1/2 : K)*h_3_3_0 + (-1/2 : K)*h_3_3_1 + (1/2 : K)*h_3_4_2 + (1/2 : K)*h_3_5_5
  have hc4 : c.coeff 4=0 := by
    linear_combination (-4)*h_0_1_0 + (-1/2 : K)*h_0_1_2 + (1/2 : K)*h_0_2_1 + -h_0_2_2 + (1/2 : K)*h_0_3_1 + (-3/2 : K)*h_0_3_2 + (1/2 : K)*h_0_4_3 + (1/2 : K)*h_0_5_6 + (1/2 : K)*h_0_0_2 + (7/2 : K)*h_0_1_1 + (3/2 : K)*h_0_2_0 + (3/2 : K)*h_0_3_3 + (1/2 : K)*h_0_3_6 + -h_0_4_4 + (1/2 : K)*h_0_4_5 + (-1/2 : K)*h_0_4_6 + -h_0_4_8 + -h_0_5_7 + (1/2 : K)*h_0_5_8 + (-1/2 : K)*h_0_0_1 + (-1/2 : K)*h_0_3_5 + h_0_4_7 + -h_0_5_9 + (1/2 : K)*h_3_2_2 + h_3_0_0 + (2)*h_3_1_2 + (3/2 : K)*h_3_2_1 + h_3_3_4 + (1/2 : K)*h_3_3_1 + -h_3_1_0 + (-1/2 : K)*h_3_3_2 + (1/2 : K)*h_3_4_3 + (1/2 : K)*h_3_5_6
  have hc5 : c.coeff 5=0 := by
    linear_combination h_3_0_1 + h_3_2_2 + h_3_3_5 + (-2)*h_3_4_7
  have hc6 : c.coeff 6=0 := by
    linear_combination (-1/2 : K)*h_0_0_0 + (12)*h_0_1_0 + h_0_1_2 + (-11/4 : K)*h_0_2_1 + (5/4 : K)*h_0_2_2 + (-9/4 : K)*h_0_3_1 + (19/4 : K)*h_0_3_2 + (-1/2 : K)*h_0_3_4 + (-9/4 : K)*h_0_4_3 + (-9/4 : K)*h_0_5_6 + (-1/2 : K)*h_0_0_2 + (-11)*h_0_1_1 + (-9/2 : K)*h_0_2_0 + (-9/2 : K)*h_0_3_3 + (-1/2 : K)*h_0_3_6 + (5/2 : K)*h_0_4_4 + (-2)*h_0_4_5 + (2)*h_0_4_6 + h_0_4_8 + (5/2 : K)*h_0_5_7 + (-2)*h_0_5_8 + h_0_0_1 + h_0_3_5 + (-2)*h_0_4_7 + (2)*h_0_5_9 + (-1/2 : K)*h_3_2_2 + h_3_0_2 + -h_3_1_1 + (1/2 : K)*h_3_2_0 + h_3_3_6 + -h_3_4_5 + (-2)*h_3_4_8 + (1/2 : K)*h_3_3_0 + -h_3_3_1 + (1/2 : K)*h_3_4_2 + (1/2 : K)*h_3_5_5 + h_3_1_0 + (1/2 : K)*h_3_3_2 + (-1/2 : K)*h_3_4_3 + (-1/2 : K)*h_3_5_6
  have hc7 : c.coeff 7=0 := by
    linear_combination (-1/2 : K)*h_4_0_1 + (-1/2 : K)*h_4_2_2 + (-1/2 : K)*h_4_3_5 + h_4_4_7
  have hc8 : c.coeff 8=0 := by
    linear_combination (-1/2 : K)*h_3_0_1 + (-1/2 : K)*h_3_2_2 + (-1/2 : K)*h_3_3_5 + h_3_4_7 + (-1/2 : K)*h_4_0_0 + (-1/2 : K)*h_4_0_2 + (3/2 : K)*h_4_1_1 + -h_4_1_2 + (1/2 : K)*h_4_2_0 + (-1/2 : K)*h_4_2_1 + (1/2 : K)*h_4_3_3 + (-1/2 : K)*h_4_3_4 + (-1/2 : K)*h_4_3_6 + (1/2 : K)*h_4_4_5 + h_4_4_8
  apply Polynomial.ext
  intro k
  by_cases hk : k≤8
  · interval_cases k <;> simp [hc0,hc1,hc2,hc3,hc4,hc5,hc6,hc7,hc8]
  · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hc (by omega)),coeff_zero]

set_option maxHeartbeats 1200000 in
theorem mixedOneThreeBase3_critical
    (E : Matrix (Fin 6) (Fin 9) K[X]) (c : K[X])
    (hE : ∀ i x, (E i x).natDegree ≤ (if i.val < 3 then 6 else 5))
    (hc : c.natDegree≤9)
    (hrel : E*mixedOneThreeBase3=(-c) • (1 : Matrix (Fin 6) (Fin 6) K[X]))
    (hsel0 : c.coeff 0=0)
    : c=0 := by
  have hz0 (x : Fin 9) (k : ℕ) (hk : 6<k) : (E 0 x).coeff k=0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (by simpa using hE 0 x) hk)
  have hz1 (x : Fin 9) (k : ℕ) (hk : 6<k) : (E 1 x).coeff k=0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (by simpa using hE 1 x) hk)
  have hz2 (x : Fin 9) (k : ℕ) (hk : 6<k) : (E 2 x).coeff k=0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (by simpa using hE 2 x) hk)
  have hz3 (x : Fin 9) (k : ℕ) (hk : 5<k) : (E 3 x).coeff k=0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (by simpa using hE 3 x) hk)
  have hz4 (x : Fin 9) (k : ℕ) (hk : 5<k) : (E 4 x).coeff k=0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (by simpa using hE 4 x) hk)
  have hz5 (x : Fin 9) (k : ℕ) (hk : 5<k) : (E 5 x).coeff k=0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (by simpa using hE 5 x) hk)
  have h (i j : Fin 6) (k : ℕ) := scalar_relation_coeff E c hrel i j k
  have h_3_0_0 : -(E 3 3).coeff 0=0 := by
    have hh := h 3 0 0
    rw [if_neg (show (3 : Fin 6) ≠ 0 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_0_1 : -(E 3 3).coeff 1=0 := by
    have hh := h 3 0 1
    rw [if_neg (show (3 : Fin 6) ≠ 0 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_0_2 : -(E 3 3).coeff 2=0 := by
    have hh := h 3 0 2
    rw [if_neg (show (3 : Fin 6) ≠ 0 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_1_0 : -(E 3 4).coeff 0=0 := by
    have hh := h 3 1 0
    rw [if_neg (show (3 : Fin 6) ≠ 1 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_1_1 : -(E 3 4).coeff 1=0 := by
    have hh := h 3 1 1
    rw [if_neg (show (3 : Fin 6) ≠ 1 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_1_2 : -(E 3 4).coeff 2=0 := by
    have hh := h 3 1 2
    rw [if_neg (show (3 : Fin 6) ≠ 1 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_2_0 : -(E 3 5).coeff 0=0 := by
    have hh := h 3 2 0
    rw [if_neg (show (3 : Fin 6) ≠ 2 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_2_1 : -(E 3 5).coeff 1=0 := by
    have hh := h 3 2 1
    rw [if_neg (show (3 : Fin 6) ≠ 2 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_2_2 : -(E 3 5).coeff 2=0 := by
    have hh := h 3 2 2
    rw [if_neg (show (3 : Fin 6) ≠ 2 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_3_1 : -(E 3 6).coeff 1 + c.coeff 1=0 := by
    have hh := h 3 3 1
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_3_2 : (2)*(E 3 4).coeff 0 + -(E 3 6).coeff 2 + c.coeff 2=0 := by
    have hh := h 3 3 2
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_3_3 : (2)*(E 3 4).coeff 1 + (E 3 5).coeff 0 + -(E 3 6).coeff 3 + c.coeff 3=0 := by
    have hh := h 3 3 3
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_3_4 : (E 3 3).coeff 0 + (2)*(E 3 4).coeff 2 + (E 3 5).coeff 1 + -(E 3 6).coeff 4 + c.coeff 4=0 := by
    have hh := h 3 3 4
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_3_5 : (E 3 3).coeff 1 + (2)*(E 3 4).coeff 3 + (E 3 5).coeff 2 + -(E 3 6).coeff 5 + c.coeff 5=0 := by
    have hh := h 3 3 5
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_3_6 : (E 3 3).coeff 2 + (2)*(E 3 4).coeff 4 + (E 3 5).coeff 3 + c.coeff 6=0 := by
    have hh := h 3 3 6
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_4_3 : (E 3 5).coeff 1 + -(E 3 6).coeff 2 + (E 3 6).coeff 1 + -(E 3 7).coeff 3=0 := by
    have hh := h 3 4 3
    rw [if_neg (show (3 : Fin 6) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_4_4 : (E 3 4).coeff 0 + (E 3 5).coeff 2 + -(E 3 6).coeff 3 + (E 3 6).coeff 2 + -(E 3 7).coeff 4=0 := by
    have hh := h 3 4 4
    rw [if_neg (show (3 : Fin 6) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_4_5 : (E 3 4).coeff 1 + (E 3 5).coeff 3 + -(E 3 6).coeff 4 + (E 3 6).coeff 3 + -(E 3 7).coeff 5=0 := by
    have hh := h 3 4 5
    rw [if_neg (show (3 : Fin 6) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_4_6 : (E 3 4).coeff 2 + (E 3 5).coeff 4 + -(E 3 6).coeff 5 + (E 3 6).coeff 4=0 := by
    have hh := h 3 4 6
    rw [if_neg (show (3 : Fin 6) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_4_7 : (E 3 4).coeff 3 + (E 3 5).coeff 5 + (E 3 6).coeff 5=0 := by
    have hh := h 3 4 7
    rw [if_neg (show (3 : Fin 6) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_4_8 : (E 3 4).coeff 4=0 := by
    have hh := h 3 4 8
    rw [if_neg (show (3 : Fin 6) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_5_6 : (E 3 5).coeff 2 + (2)*(E 3 6).coeff 4 + (E 3 7).coeff 3=0 := by
    have hh := h 3 5 6
    rw [if_neg (show (3 : Fin 6) ≠ 5 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_5_7 : (E 3 5).coeff 3 + (2)*(E 3 6).coeff 5 + (E 3 7).coeff 4=0 := by
    have hh := h 3 5 7
    rw [if_neg (show (3 : Fin 6) ≠ 5 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_5_8 : (E 3 5).coeff 4 + (E 3 7).coeff 5=0 := by
    have hh := h 3 5 8
    rw [if_neg (show (3 : Fin 6) ≠ 5 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_3_5_9 : (E 3 5).coeff 5=0 := by
    have hh := h 3 5 9
    rw [if_neg (show (3 : Fin 6) ≠ 5 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_0_0 : -(E 4 3).coeff 0=0 := by
    have hh := h 4 0 0
    rw [if_neg (show (4 : Fin 6) ≠ 0 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_0_1 : -(E 4 3).coeff 1=0 := by
    have hh := h 4 0 1
    rw [if_neg (show (4 : Fin 6) ≠ 0 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_0_2 : -(E 4 3).coeff 2=0 := by
    have hh := h 4 0 2
    rw [if_neg (show (4 : Fin 6) ≠ 0 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_1_0 : -(E 4 4).coeff 0=0 := by
    have hh := h 4 1 0
    rw [if_neg (show (4 : Fin 6) ≠ 1 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_1_1 : -(E 4 4).coeff 1=0 := by
    have hh := h 4 1 1
    rw [if_neg (show (4 : Fin 6) ≠ 1 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_1_2 : -(E 4 4).coeff 2=0 := by
    have hh := h 4 1 2
    rw [if_neg (show (4 : Fin 6) ≠ 1 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_2_0 : -(E 4 5).coeff 0=0 := by
    have hh := h 4 2 0
    rw [if_neg (show (4 : Fin 6) ≠ 2 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_2_1 : -(E 4 5).coeff 1=0 := by
    have hh := h 4 2 1
    rw [if_neg (show (4 : Fin 6) ≠ 2 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_2_2 : -(E 4 5).coeff 2=0 := by
    have hh := h 4 2 2
    rw [if_neg (show (4 : Fin 6) ≠ 2 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_3_1 : -(E 4 6).coeff 1=0 := by
    have hh := h 4 3 1
    rw [if_neg (show (4 : Fin 6) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_3_2 : (2)*(E 4 4).coeff 0 + -(E 4 6).coeff 2=0 := by
    have hh := h 4 3 2
    rw [if_neg (show (4 : Fin 6) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_3_3 : (2)*(E 4 4).coeff 1 + (E 4 5).coeff 0 + -(E 4 6).coeff 3=0 := by
    have hh := h 4 3 3
    rw [if_neg (show (4 : Fin 6) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_3_4 : (E 4 3).coeff 0 + (2)*(E 4 4).coeff 2 + (E 4 5).coeff 1 + -(E 4 6).coeff 4=0 := by
    have hh := h 4 3 4
    rw [if_neg (show (4 : Fin 6) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_3_5 : (E 4 3).coeff 1 + (2)*(E 4 4).coeff 3 + (E 4 5).coeff 2 + -(E 4 6).coeff 5=0 := by
    have hh := h 4 3 5
    rw [if_neg (show (4 : Fin 6) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_3_6 : (E 4 3).coeff 2 + (2)*(E 4 4).coeff 4 + (E 4 5).coeff 3=0 := by
    have hh := h 4 3 6
    rw [if_neg (show (4 : Fin 6) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_4_3 : (E 4 5).coeff 1 + -(E 4 6).coeff 2 + (E 4 6).coeff 1 + -(E 4 7).coeff 3 + c.coeff 3=0 := by
    have hh := h 4 4 3
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_4_4 : (E 4 4).coeff 0 + (E 4 5).coeff 2 + -(E 4 6).coeff 3 + (E 4 6).coeff 2 + -(E 4 7).coeff 4 + c.coeff 4=0 := by
    have hh := h 4 4 4
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_4_5 : (E 4 4).coeff 1 + (E 4 5).coeff 3 + -(E 4 6).coeff 4 + (E 4 6).coeff 3 + -(E 4 7).coeff 5 + c.coeff 5=0 := by
    have hh := h 4 4 5
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_4_6 : (E 4 4).coeff 2 + (E 4 5).coeff 4 + -(E 4 6).coeff 5 + (E 4 6).coeff 4 + c.coeff 6=0 := by
    have hh := h 4 4 6
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_4_7 : (E 4 4).coeff 3 + (E 4 5).coeff 5 + (E 4 6).coeff 5 + c.coeff 7=0 := by
    have hh := h 4 4 7
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_4_8 : (E 4 4).coeff 4 + c.coeff 8=0 := by
    have hh := h 4 4 8
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_5_6 : (E 4 5).coeff 2 + (2)*(E 4 6).coeff 4 + (E 4 7).coeff 3=0 := by
    have hh := h 4 5 6
    rw [if_neg (show (4 : Fin 6) ≠ 5 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_5_7 : (E 4 5).coeff 3 + (2)*(E 4 6).coeff 5 + (E 4 7).coeff 4=0 := by
    have hh := h 4 5 7
    rw [if_neg (show (4 : Fin 6) ≠ 5 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_5_8 : (E 4 5).coeff 4 + (E 4 7).coeff 5=0 := by
    have hh := h 4 5 8
    rw [if_neg (show (4 : Fin 6) ≠ 5 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_4_5_9 : (E 4 5).coeff 5=0 := by
    have hh := h 4 5 9
    rw [if_neg (show (4 : Fin 6) ≠ 5 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_0_0 : -(E 5 3).coeff 0=0 := by
    have hh := h 5 0 0
    rw [if_neg (show (5 : Fin 6) ≠ 0 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_0_1 : -(E 5 3).coeff 1=0 := by
    have hh := h 5 0 1
    rw [if_neg (show (5 : Fin 6) ≠ 0 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_0_2 : -(E 5 3).coeff 2=0 := by
    have hh := h 5 0 2
    rw [if_neg (show (5 : Fin 6) ≠ 0 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_1_0 : -(E 5 4).coeff 0=0 := by
    have hh := h 5 1 0
    rw [if_neg (show (5 : Fin 6) ≠ 1 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_1_1 : -(E 5 4).coeff 1=0 := by
    have hh := h 5 1 1
    rw [if_neg (show (5 : Fin 6) ≠ 1 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_1_2 : -(E 5 4).coeff 2=0 := by
    have hh := h 5 1 2
    rw [if_neg (show (5 : Fin 6) ≠ 1 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_2_0 : -(E 5 5).coeff 0=0 := by
    have hh := h 5 2 0
    rw [if_neg (show (5 : Fin 6) ≠ 2 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_2_1 : -(E 5 5).coeff 1=0 := by
    have hh := h 5 2 1
    rw [if_neg (show (5 : Fin 6) ≠ 2 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_2_2 : -(E 5 5).coeff 2=0 := by
    have hh := h 5 2 2
    rw [if_neg (show (5 : Fin 6) ≠ 2 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_3_1 : -(E 5 6).coeff 1=0 := by
    have hh := h 5 3 1
    rw [if_neg (show (5 : Fin 6) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_3_2 : (2)*(E 5 4).coeff 0 + -(E 5 6).coeff 2=0 := by
    have hh := h 5 3 2
    rw [if_neg (show (5 : Fin 6) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_3_3 : (2)*(E 5 4).coeff 1 + (E 5 5).coeff 0 + -(E 5 6).coeff 3=0 := by
    have hh := h 5 3 3
    rw [if_neg (show (5 : Fin 6) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_3_4 : (E 5 3).coeff 0 + (2)*(E 5 4).coeff 2 + (E 5 5).coeff 1 + -(E 5 6).coeff 4=0 := by
    have hh := h 5 3 4
    rw [if_neg (show (5 : Fin 6) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_3_5 : (E 5 3).coeff 1 + (2)*(E 5 4).coeff 3 + (E 5 5).coeff 2 + -(E 5 6).coeff 5=0 := by
    have hh := h 5 3 5
    rw [if_neg (show (5 : Fin 6) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_3_6 : (E 5 3).coeff 2 + (2)*(E 5 4).coeff 4 + (E 5 5).coeff 3=0 := by
    have hh := h 5 3 6
    rw [if_neg (show (5 : Fin 6) ≠ 3 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_4_3 : (E 5 5).coeff 1 + -(E 5 6).coeff 2 + (E 5 6).coeff 1 + -(E 5 7).coeff 3=0 := by
    have hh := h 5 4 3
    rw [if_neg (show (5 : Fin 6) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_4_4 : (E 5 4).coeff 0 + (E 5 5).coeff 2 + -(E 5 6).coeff 3 + (E 5 6).coeff 2 + -(E 5 7).coeff 4=0 := by
    have hh := h 5 4 4
    rw [if_neg (show (5 : Fin 6) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_4_5 : (E 5 4).coeff 1 + (E 5 5).coeff 3 + -(E 5 6).coeff 4 + (E 5 6).coeff 3 + -(E 5 7).coeff 5=0 := by
    have hh := h 5 4 5
    rw [if_neg (show (5 : Fin 6) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_4_6 : (E 5 4).coeff 2 + (E 5 5).coeff 4 + -(E 5 6).coeff 5 + (E 5 6).coeff 4=0 := by
    have hh := h 5 4 6
    rw [if_neg (show (5 : Fin 6) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_4_7 : (E 5 4).coeff 3 + (E 5 5).coeff 5 + (E 5 6).coeff 5=0 := by
    have hh := h 5 4 7
    rw [if_neg (show (5 : Fin 6) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_4_8 : (E 5 4).coeff 4=0 := by
    have hh := h 5 4 8
    rw [if_neg (show (5 : Fin 6) ≠ 4 by decide)] at hh
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_5_6 : (E 5 5).coeff 2 + (2)*(E 5 6).coeff 4 + (E 5 7).coeff 3 + c.coeff 6=0 := by
    have hh := h 5 5 6
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_5_7 : (E 5 5).coeff 3 + (2)*(E 5 6).coeff 5 + (E 5 7).coeff 4 + c.coeff 7=0 := by
    have hh := h 5 5 7
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_5_8 : (E 5 5).coeff 4 + (E 5 7).coeff 5 + c.coeff 8=0 := by
    have hh := h 5 5 8
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have h_5_5_9 : (E 5 5).coeff 5 + c.coeff 9=0 := by
    have hh := h 5 5 9
    norm_num [mixedOneThreeBase3,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,mul_neg,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      matrix_cons_five,matrix_cons_six,matrix_cons_seven,matrix_cons_eight,matrix_cons_nine,
      coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2,hz3,hz4,hz5] at hh
    first | linear_combination (norm := ring1!) hh | linear_combination (norm := ring1!) -hh
  have hc0 : c.coeff 0=0 := by
    linear_combination hsel0
  have hc1 : c.coeff 1=0 := by
    linear_combination (6/7 : K)*h_3_0_0 + h_3_1_0 + (8/7 : K)*h_3_1_2 + (13/7 : K)*h_3_2_1 + (20/7 : K)*h_3_2_2 + h_3_3_1 + (6/7 : K)*h_3_3_4 + h_3_4_3 + h_3_5_6 + (-11/7 : K)*h_3_0_2 + (-2/7 : K)*h_3_1_1 + (-3/7 : K)*h_3_2_0 + (-3/7 : K)*h_3_3_3 + (-11/7 : K)*h_3_3_6 + h_3_4_4 + (4/7 : K)*h_3_4_5 + (-4/7 : K)*h_3_4_6 + (22/7 : K)*h_3_4_8 + h_3_5_7 + (4/7 : K)*h_3_5_8 + (6/7 : K)*h_3_0_1 + (6/7 : K)*h_3_3_5 + (-12/7 : K)*h_3_4_7 + (12/7 : K)*h_3_5_9 + (18/7 : K)*h_4_0_0 + (-24/7 : K)*h_4_1_0 + (6)*h_4_1_2 + (3)*h_4_2_1 + (-9/7 : K)*h_4_2_2 + (3/7 : K)*h_4_3_1 + (-9/7 : K)*h_4_3_2 + (18/7 : K)*h_4_3_4 + (3/7 : K)*h_4_4_3 + (3/7 : K)*h_4_5_6 + (12/7 : K)*h_4_0_2 + (-6/7 : K)*h_4_1_1 + (12/7 : K)*h_4_3_6 + (-6/7 : K)*h_4_4_4 + (-6/7 : K)*h_4_4_5 + (6/7 : K)*h_4_4_6 + (-24/7 : K)*h_4_4_8 + (-6/7 : K)*h_4_5_7 + (-6/7 : K)*h_4_5_8 + (-6/7 : K)*h_4_0_1 + (-6/7 : K)*h_4_3_5 + (12/7 : K)*h_4_4_7 + (-12/7 : K)*h_4_5_9 + (-38/7 : K)*h_5_0_0 + (-46/7 : K)*h_5_1_0 + (-100/7 : K)*h_5_1_2 + (-33/7 : K)*h_5_2_1 + -h_5_2_2 + (5/7 : K)*h_5_3_1 + (-17/7 : K)*h_5_3_2 + (-38/7 : K)*h_5_3_4 + (5/7 : K)*h_5_4_3 + (5/7 : K)*h_5_5_6 + (-12/7 : K)*h_5_0_2 + (96/7 : K)*h_5_1_1 + (36/7 : K)*h_5_2_0 + (36/7 : K)*h_5_3_3 + (-12/7 : K)*h_5_3_6 + (-12/7 : K)*h_5_4_4 + (24/7 : K)*h_5_4_5 + (-24/7 : K)*h_5_4_6 + (24/7 : K)*h_5_4_8 + (-12/7 : K)*h_5_5_7 + (24/7 : K)*h_5_5_8
  have hc2 : c.coeff 2=0 := by
    linear_combination (4/7 : K)*h_3_0_0 + (3)*h_3_1_0 + (10/7 : K)*h_3_1_2 + (4/7 : K)*h_3_2_1 + (11/7 : K)*h_3_2_2 + h_3_3_2 + (4/7 : K)*h_3_3_4 + (-5/7 : K)*h_3_0_2 + (-20/7 : K)*h_3_1_1 + (-9/7 : K)*h_3_2_0 + (-9/7 : K)*h_3_3_3 + (-5/7 : K)*h_3_3_6 + h_3_4_4 + (-2/7 : K)*h_3_4_5 + (2/7 : K)*h_3_4_6 + (10/7 : K)*h_3_4_8 + h_3_5_7 + (-2/7 : K)*h_3_5_8 + (4/7 : K)*h_3_0_1 + (4/7 : K)*h_3_3_5 + (-8/7 : K)*h_3_4_7 + (8/7 : K)*h_3_5_9 + (26/7 : K)*h_4_0_0 + (-30/7 : K)*h_4_1_0 + (8)*h_4_1_2 + (5)*h_4_2_1 + (1/7 : K)*h_4_2_2 + (9/7 : K)*h_4_3_1 + (-13/7 : K)*h_4_3_2 + (26/7 : K)*h_4_3_4 + (9/7 : K)*h_4_4_3 + (9/7 : K)*h_4_5_6 + (8/7 : K)*h_4_0_2 + (-4/7 : K)*h_4_1_1 + (8/7 : K)*h_4_3_6 + (-4/7 : K)*h_4_4_4 + (-4/7 : K)*h_4_4_5 + (4/7 : K)*h_4_4_6 + (-16/7 : K)*h_4_4_8 + (-4/7 : K)*h_4_5_7 + (-4/7 : K)*h_4_5_8 + (-4/7 : K)*h_4_0_1 + (-4/7 : K)*h_4_3_5 + (8/7 : K)*h_4_4_7 + (-8/7 : K)*h_4_5_9 + (-30/7 : K)*h_5_0_0 + (-26/7 : K)*h_5_1_0 + (-76/7 : K)*h_5_1_2 + (-29/7 : K)*h_5_2_1 + -h_5_2_2 + (1/7 : K)*h_5_3_1 + (-9/7 : K)*h_5_3_2 + (-30/7 : K)*h_5_3_4 + (1/7 : K)*h_5_4_3 + (1/7 : K)*h_5_5_6 + (-8/7 : K)*h_5_0_2 + (64/7 : K)*h_5_1_1 + (24/7 : K)*h_5_2_0 + (24/7 : K)*h_5_3_3 + (-8/7 : K)*h_5_3_6 + (-8/7 : K)*h_5_4_4 + (16/7 : K)*h_5_4_5 + (-16/7 : K)*h_5_4_6 + (16/7 : K)*h_5_4_8 + (-8/7 : K)*h_5_5_7 + (16/7 : K)*h_5_5_8
  have hc3 : c.coeff 3=0 := by
    linear_combination (2)*h_4_0_0 + (-2)*h_4_1_0 + (4)*h_4_1_2 + (3)*h_4_2_1 + h_4_2_2 + h_4_3_1 + -h_4_3_2 + (2)*h_4_3_4 + h_4_4_3 + h_4_5_6
  have hc4 : c.coeff 4=0 := by
    linear_combination (6/7 : K)*h_3_0_0 + (15/7 : K)*h_3_1_2 + (6/7 : K)*h_3_2_1 + (-1/7 : K)*h_3_2_2 + (6/7 : K)*h_3_3_4 + (3/7 : K)*h_3_0_2 + (-9/7 : K)*h_3_1_1 + (-3/7 : K)*h_3_2_0 + (-3/7 : K)*h_3_3_3 + (3/7 : K)*h_3_3_6 + (-3/7 : K)*h_3_4_5 + (3/7 : K)*h_3_4_6 + (-6/7 : K)*h_3_4_8 + (-3/7 : K)*h_3_5_8 + (-1/7 : K)*h_3_0_1 + (-1/7 : K)*h_3_3_5 + (2/7 : K)*h_3_4_7 + (-2/7 : K)*h_3_5_9 + (4/7 : K)*h_4_0_0 + (-3/7 : K)*h_4_1_0 + h_4_1_2 + h_4_2_1 + (5/7 : K)*h_4_2_2 + (3/7 : K)*h_4_3_1 + (-2/7 : K)*h_4_3_2 + (4/7 : K)*h_4_3_4 + (3/7 : K)*h_4_4_3 + (3/7 : K)*h_4_5_6 + (-2/7 : K)*h_4_0_2 + (1/7 : K)*h_4_1_1 + (-2/7 : K)*h_4_3_6 + (1/7 : K)*h_4_4_4 + (1/7 : K)*h_4_4_5 + (-1/7 : K)*h_4_4_6 + (4/7 : K)*h_4_4_8 + (1/7 : K)*h_4_5_7 + (1/7 : K)*h_4_5_8 + (1/7 : K)*h_4_0_1 + (1/7 : K)*h_4_3_5 + (-2/7 : K)*h_4_4_7 + (2/7 : K)*h_4_5_9 + (4/7 : K)*h_5_0_0 + (10/7 : K)*h_5_1_0 + (12/7 : K)*h_5_1_2 + (2/7 : K)*h_5_2_1 + (-2/7 : K)*h_5_3_1 + (4/7 : K)*h_5_3_2 + (4/7 : K)*h_5_3_4 + (-2/7 : K)*h_5_4_3 + (-2/7 : K)*h_5_5_6 + (2/7 : K)*h_5_0_2 + (-16/7 : K)*h_5_1_1 + (-6/7 : K)*h_5_2_0 + (-6/7 : K)*h_5_3_3 + (2/7 : K)*h_5_3_6 + (2/7 : K)*h_5_4_4 + (-4/7 : K)*h_5_4_5 + (4/7 : K)*h_5_4_6 + (-4/7 : K)*h_5_4_8 + (2/7 : K)*h_5_5_7 + (-4/7 : K)*h_5_5_8
  have hc5 : c.coeff 5=0 := by
    linear_combination (-6/7 : K)*h_3_0_0 + (-15/7 : K)*h_3_1_2 + (-6/7 : K)*h_3_2_1 + (1/7 : K)*h_3_2_2 + (-6/7 : K)*h_3_3_4 + (-3/7 : K)*h_3_0_2 + (9/7 : K)*h_3_1_1 + (3/7 : K)*h_3_2_0 + (3/7 : K)*h_3_3_3 + (-3/7 : K)*h_3_3_6 + (3/7 : K)*h_3_4_5 + (-3/7 : K)*h_3_4_6 + (6/7 : K)*h_3_4_8 + (3/7 : K)*h_3_5_8 + (1/7 : K)*h_3_0_1 + (1/7 : K)*h_3_3_5 + (-2/7 : K)*h_3_4_7 + (2/7 : K)*h_3_5_9 + (-18/7 : K)*h_4_0_0 + (24/7 : K)*h_4_1_0 + (-6)*h_4_1_2 + (-3)*h_4_2_1 + (9/7 : K)*h_4_2_2 + (-3/7 : K)*h_4_3_1 + (9/7 : K)*h_4_3_2 + (-18/7 : K)*h_4_3_4 + (-3/7 : K)*h_4_4_3 + (-3/7 : K)*h_4_5_6 + (-12/7 : K)*h_4_0_2 + (6/7 : K)*h_4_1_1 + (-12/7 : K)*h_4_3_6 + (6/7 : K)*h_4_4_4 + (6/7 : K)*h_4_4_5 + (-6/7 : K)*h_4_4_6 + (24/7 : K)*h_4_4_8 + (6/7 : K)*h_4_5_7 + (6/7 : K)*h_4_5_8 + (6/7 : K)*h_4_0_1 + (6/7 : K)*h_4_3_5 + (-12/7 : K)*h_4_4_7 + (12/7 : K)*h_4_5_9 + (66/7 : K)*h_5_0_0 + (18/7 : K)*h_5_1_0 + (156/7 : K)*h_5_1_2 + (75/7 : K)*h_5_2_1 + (3)*h_5_2_2 + (9/7 : K)*h_5_3_1 + (3/7 : K)*h_5_3_2 + (66/7 : K)*h_5_3_4 + (9/7 : K)*h_5_4_3 + (9/7 : K)*h_5_5_6 + (12/7 : K)*h_5_0_2 + (-96/7 : K)*h_5_1_1 + (-36/7 : K)*h_5_2_0 + (-36/7 : K)*h_5_3_3 + (12/7 : K)*h_5_3_6 + (12/7 : K)*h_5_4_4 + (-24/7 : K)*h_5_4_5 + (24/7 : K)*h_5_4_6 + (-24/7 : K)*h_5_4_8 + (12/7 : K)*h_5_5_7 + (-24/7 : K)*h_5_5_8
  have hc6 : c.coeff 6=0 := by
    linear_combination (2)*h_5_0_0 + (-2)*h_5_1_0 + (4)*h_5_1_2 + (3)*h_5_2_1 + h_5_2_2 + h_5_3_1 + -h_5_3_2 + (2)*h_5_3_4 + h_5_4_3 + h_5_5_6
  have hc7 : c.coeff 7=0 := by
    linear_combination (18/7 : K)*h_3_0_0 + (45/7 : K)*h_3_1_2 + (18/7 : K)*h_3_2_1 + (-3/7 : K)*h_3_2_2 + (18/7 : K)*h_3_3_4 + (9/7 : K)*h_3_0_2 + (-27/7 : K)*h_3_1_1 + (-9/7 : K)*h_3_2_0 + (-9/7 : K)*h_3_3_3 + (9/7 : K)*h_3_3_6 + (-9/7 : K)*h_3_4_5 + (9/7 : K)*h_3_4_6 + (-18/7 : K)*h_3_4_8 + (-9/7 : K)*h_3_5_8 + (-3/7 : K)*h_3_0_1 + (-3/7 : K)*h_3_3_5 + (6/7 : K)*h_3_4_7 + (-6/7 : K)*h_3_5_9 + (12/7 : K)*h_4_0_0 + (-72/7 : K)*h_4_1_0 + (3)*h_4_1_2 + (3)*h_4_2_1 + (-20/7 : K)*h_4_2_2 + (9/7 : K)*h_4_3_1 + (-27/7 : K)*h_4_3_2 + (12/7 : K)*h_4_3_4 + (9/7 : K)*h_4_4_3 + (9/7 : K)*h_4_5_6 + (15/7 : K)*h_4_0_2 + (45/7 : K)*h_4_1_1 + (3)*h_4_2_0 + (3)*h_4_3_3 + (15/7 : K)*h_4_3_6 + (-18/7 : K)*h_4_4_4 + (3/7 : K)*h_4_4_5 + (-3/7 : K)*h_4_4_6 + (-30/7 : K)*h_4_4_8 + (-18/7 : K)*h_4_5_7 + (3/7 : K)*h_4_5_8 + (-11/7 : K)*h_4_0_1 + (-11/7 : K)*h_4_3_5 + (22/7 : K)*h_4_4_7 + (-22/7 : K)*h_4_5_9 + (-72/7 : K)*h_5_0_0 + (-33/7 : K)*h_5_1_0 + (-174/7 : K)*h_5_1_2 + (-78/7 : K)*h_5_2_1 + (-3)*h_5_2_2 + (-6/7 : K)*h_5_3_1 + (-9/7 : K)*h_5_3_2 + (-72/7 : K)*h_5_3_4 + (-6/7 : K)*h_5_4_3 + (-6/7 : K)*h_5_5_6 + (-15/7 : K)*h_5_0_2 + (120/7 : K)*h_5_1_1 + (45/7 : K)*h_5_2_0 + (45/7 : K)*h_5_3_3 + (-15/7 : K)*h_5_3_6 + (-15/7 : K)*h_5_4_4 + (30/7 : K)*h_5_4_5 + (-30/7 : K)*h_5_4_6 + (30/7 : K)*h_5_4_8 + (-15/7 : K)*h_5_5_7 + (30/7 : K)*h_5_5_8
  have hc8 : c.coeff 8=0 := by
    linear_combination (9/7 : K)*h_3_0_0 + (45/14 : K)*h_3_1_2 + (9/7 : K)*h_3_2_1 + (-3/14 : K)*h_3_2_2 + (9/7 : K)*h_3_3_4 + (9/14 : K)*h_3_0_2 + (-27/14 : K)*h_3_1_1 + (-9/14 : K)*h_3_2_0 + (-9/14 : K)*h_3_3_3 + (9/14 : K)*h_3_3_6 + (-9/14 : K)*h_3_4_5 + (9/14 : K)*h_3_4_6 + (-9/7 : K)*h_3_4_8 + (-9/14 : K)*h_3_5_8 + (-3/14 : K)*h_3_0_1 + (-3/14 : K)*h_3_3_5 + (3/7 : K)*h_3_4_7 + (-3/7 : K)*h_3_5_9 + (6/7 : K)*h_4_0_0 + (-36/7 : K)*h_4_1_0 + (3/2 : K)*h_4_1_2 + (3/2 : K)*h_4_2_1 + (-10/7 : K)*h_4_2_2 + (9/14 : K)*h_4_3_1 + (-27/14 : K)*h_4_3_2 + (6/7 : K)*h_4_3_4 + (9/14 : K)*h_4_4_3 + (9/14 : K)*h_4_5_6 + (15/14 : K)*h_4_0_2 + (45/14 : K)*h_4_1_1 + (3/2 : K)*h_4_2_0 + (3/2 : K)*h_4_3_3 + (15/14 : K)*h_4_3_6 + (-9/7 : K)*h_4_4_4 + (3/14 : K)*h_4_4_5 + (-3/14 : K)*h_4_4_6 + (-15/7 : K)*h_4_4_8 + (-9/7 : K)*h_4_5_7 + (3/14 : K)*h_4_5_8 + (-11/14 : K)*h_4_0_1 + (-11/14 : K)*h_4_3_5 + (11/7 : K)*h_4_4_7 + (-11/7 : K)*h_4_5_9 + (-50/7 : K)*h_5_0_0 + (-27/7 : K)*h_5_1_0 + (-122/7 : K)*h_5_1_2 + (-53/7 : K)*h_5_2_1 + (-2)*h_5_2_2 + (-3/7 : K)*h_5_3_1 + (-8/7 : K)*h_5_3_2 + (-50/7 : K)*h_5_3_4 + (-3/7 : K)*h_5_4_3 + (-3/7 : K)*h_5_5_6 + (-11/7 : K)*h_5_0_2 + (88/7 : K)*h_5_1_1 + (33/7 : K)*h_5_2_0 + (33/7 : K)*h_5_3_3 + (-11/7 : K)*h_5_3_6 + (-11/7 : K)*h_5_4_4 + (22/7 : K)*h_5_4_5 + (-22/7 : K)*h_5_4_6 + (22/7 : K)*h_5_4_8 + (-11/7 : K)*h_5_5_7 + (22/7 : K)*h_5_5_8
  have hc9 : c.coeff 9=0 := by
    linear_combination (-27/14 : K)*h_3_0_0 + (-135/28 : K)*h_3_1_2 + (-27/14 : K)*h_3_2_1 + (9/28 : K)*h_3_2_2 + (-27/14 : K)*h_3_3_4 + (-27/28 : K)*h_3_0_2 + (81/28 : K)*h_3_1_1 + (27/28 : K)*h_3_2_0 + (27/28 : K)*h_3_3_3 + (-27/28 : K)*h_3_3_6 + (27/28 : K)*h_3_4_5 + (-27/28 : K)*h_3_4_6 + (27/14 : K)*h_3_4_8 + (27/28 : K)*h_3_5_8 + (9/28 : K)*h_3_0_1 + (9/28 : K)*h_3_3_5 + (-9/14 : K)*h_3_4_7 + (9/14 : K)*h_3_5_9 + (-9/7 : K)*h_4_0_0 + (54/7 : K)*h_4_1_0 + (-9/4 : K)*h_4_1_2 + (-9/4 : K)*h_4_2_1 + (15/7 : K)*h_4_2_2 + (-27/28 : K)*h_4_3_1 + (81/28 : K)*h_4_3_2 + (-9/7 : K)*h_4_3_4 + (-27/28 : K)*h_4_4_3 + (-27/28 : K)*h_4_5_6 + (-45/28 : K)*h_4_0_2 + (-135/28 : K)*h_4_1_1 + (-9/4 : K)*h_4_2_0 + (-9/4 : K)*h_4_3_3 + (-45/28 : K)*h_4_3_6 + (27/14 : K)*h_4_4_4 + (-9/28 : K)*h_4_4_5 + (9/28 : K)*h_4_4_6 + (45/14 : K)*h_4_4_8 + (27/14 : K)*h_4_5_7 + (-9/28 : K)*h_4_5_8 + (33/28 : K)*h_4_0_1 + (33/28 : K)*h_4_3_5 + (-33/14 : K)*h_4_4_7 + (33/14 : K)*h_4_5_9 + (54/7 : K)*h_5_0_0 + (81/14 : K)*h_5_1_0 + (261/14 : K)*h_5_1_2 + (117/14 : K)*h_5_2_1 + (7/2 : K)*h_5_2_2 + (9/14 : K)*h_5_3_1 + (12/7 : K)*h_5_3_2 + (54/7 : K)*h_5_3_4 + (9/14 : K)*h_5_4_3 + (9/14 : K)*h_5_5_6 + (6/7 : K)*h_5_0_2 + (-201/14 : K)*h_5_1_1 + (-39/7 : K)*h_5_2_0 + (-39/7 : K)*h_5_3_3 + (6/7 : K)*h_5_3_6 + (33/14 : K)*h_5_4_4 + (-45/14 : K)*h_5_4_5 + (45/14 : K)*h_5_4_6 + (-12/7 : K)*h_5_4_8 + (33/14 : K)*h_5_5_7 + (-45/14 : K)*h_5_5_8 + (1/2 : K)*h_5_0_1 + (1/2 : K)*h_5_3_5 + -h_5_4_7 + h_5_5_9
  apply Polynomial.ext
  intro k
  by_cases hk : k≤9
  · interval_cases k <;> simp [hc0,hc1,hc2,hc3,hc4,hc5,hc6,hc7,hc8,hc9]
  · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hc (by omega)),coeff_zero]

end FD56
