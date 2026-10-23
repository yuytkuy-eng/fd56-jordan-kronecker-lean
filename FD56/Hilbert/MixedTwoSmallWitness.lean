/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.UniformThreeWitness

/-! A weighted scalar obstruction for dimensions ten and seven. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K : Type*} [Field K]

def mixedTwoSmallWitness : Matrix (Fin 7) (Fin 3) K[X] :=
  ![![1, X, - X^3], ![0, 1 + X^2, 0], ![0, 0, 1], ![X^4, 0, 0], ![X, - X + X^4, X^2], ![X^3, X^4, X^4], ![0, - X, X^5]]

theorem mixedTwoSmallWitness_degree (i : Fin 7) (j : Fin 3) :
    (mixedTwoSmallWitness (K := K) i j).natDegree ≤ if j = 2 then 5 else 4 := by
  fin_cases i <;> fin_cases j <;> simp [mixedTwoSmallWitness]
  all_goals exact (natDegree_add_le _ _).trans (by simp)

theorem mixedTwoSmallWitness_injective :
    Function.Injective (mixedTwoSmallWitness (K := K)).mulVec := by
  apply polynomial_matrix_injective_of_zero
  intro u v h
  funext j
  fin_cases j
  · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mixedTwoSmallWitness]
      using congrFun h (0 : Fin 7)
  · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mixedTwoSmallWitness]
      using congrFun h (1 : Fin 7)
  · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mixedTwoSmallWitness]
      using congrFun h (2 : Fin 7)

set_option maxHeartbeats 4000000 in
theorem mixedTwoSmallWitness_scalar_obstruction
    (E : Matrix (Fin 3) (Fin 7) K[X]) (c : K[X])
    (hE : ∀ i j, (E i j).natDegree ≤ if i = 2 then 1 else 2)
    (hrel : E * mixedTwoSmallWitness = (-c) • (1 : Matrix (Fin 3) (Fin 3) K[X])) :
    E = 0 ∧ c = 0 := by
  have hn02 : (0 : Fin 3) ≠ 2 := by decide
  have hn12 : (1 : Fin 3) ≠ 2 := by decide
  have hcE (i : Fin 3) (j : Fin 7) (d : ℕ)
      (hd : (if i = 2 then 1 else 2) < d) : (E i j).coeff d = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hE i j) hd)
  have hentry (i j : Fin 3) :
      (E * mixedTwoSmallWitness (K := K)) i j + (if i = j then c else 0) = 0 := by
    have h := congrArg (fun A : Matrix (Fin 3) (Fin 3) K[X] => A i j) hrel
    by_cases hij : i = j <;> simp [hij, Matrix.smul_apply, Matrix.one_apply] at h ⊢ <;>
      linear_combination h
  have h0 (i : Fin 3) :
      E i 0 + E i 3 * X^4 + E i 4 * X + E i 5 * X^3 + (if i = 0 then c else 0) = 0 := by
    simpa [mixedTwoSmallWitness,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,sub_eq_add_neg,add_assoc]
      using hentry i 0
  have h1 (i : Fin 3) :
      E i 0 * X + E i 1 + E i 1 * X^2 - E i 4 * X + E i 4 * X^4 + E i 5 * X^4 - E i 6 * X + (if i = 1 then c else 0) = 0 := by
    simpa [mixedTwoSmallWitness,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,sub_eq_add_neg,add_assoc]
      using hentry i 1
  have h2 (i : Fin 3) :
      - E i 0 * X^3 + E i 2 + E i 4 * X^2 + E i 5 * X^4 + E i 6 * X^5 + (if i = 2 then c else 0) = 0 := by
    simpa [mixedTwoSmallWitness,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,mul_sub,sub_eq_add_neg,add_assoc]
      using hentry i 2
  have h000 := congrArg (fun p : K[X] => p.coeff 0) (h0 0)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h000
  have h001 := congrArg (fun p : K[X] => p.coeff 1) (h0 0)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h001
  have h002 := congrArg (fun p : K[X] => p.coeff 2) (h0 0)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h002
  have h003 := congrArg (fun p : K[X] => p.coeff 3) (h0 0)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h003
  have h004 := congrArg (fun p : K[X] => p.coeff 4) (h0 0)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h004
  have h005 := congrArg (fun p : K[X] => p.coeff 5) (h0 0)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h005
  have h006 := congrArg (fun p : K[X] => p.coeff 6) (h0 0)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h006
  have h010 := congrArg (fun p : K[X] => p.coeff 0) (h1 0)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h010
  have h011 := congrArg (fun p : K[X] => p.coeff 1) (h1 0)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h011
  have h012 := congrArg (fun p : K[X] => p.coeff 2) (h1 0)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h012
  have h013 := congrArg (fun p : K[X] => p.coeff 3) (h1 0)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h013
  have h014 := congrArg (fun p : K[X] => p.coeff 4) (h1 0)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h014
  have h015 := congrArg (fun p : K[X] => p.coeff 5) (h1 0)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h015
  have h016 := congrArg (fun p : K[X] => p.coeff 6) (h1 0)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h016
  have h020 := congrArg (fun p : K[X] => p.coeff 0) (h2 0)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h020
  have h021 := congrArg (fun p : K[X] => p.coeff 1) (h2 0)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h021
  have h022 := congrArg (fun p : K[X] => p.coeff 2) (h2 0)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h022
  have h023 := congrArg (fun p : K[X] => p.coeff 3) (h2 0)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h023
  have h024 := congrArg (fun p : K[X] => p.coeff 4) (h2 0)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h024
  have h025 := congrArg (fun p : K[X] => p.coeff 5) (h2 0)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h025
  have h026 := congrArg (fun p : K[X] => p.coeff 6) (h2 0)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h026
  have h027 := congrArg (fun p : K[X] => p.coeff 7) (h2 0)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h027
  have h100 := congrArg (fun p : K[X] => p.coeff 0) (h0 1)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h100
  have h101 := congrArg (fun p : K[X] => p.coeff 1) (h0 1)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h101
  have h102 := congrArg (fun p : K[X] => p.coeff 2) (h0 1)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h102
  have h103 := congrArg (fun p : K[X] => p.coeff 3) (h0 1)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h103
  have h104 := congrArg (fun p : K[X] => p.coeff 4) (h0 1)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h104
  have h105 := congrArg (fun p : K[X] => p.coeff 5) (h0 1)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h105
  have h106 := congrArg (fun p : K[X] => p.coeff 6) (h0 1)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h106
  have h110 := congrArg (fun p : K[X] => p.coeff 0) (h1 1)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h110
  have h111 := congrArg (fun p : K[X] => p.coeff 1) (h1 1)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h111
  have h112 := congrArg (fun p : K[X] => p.coeff 2) (h1 1)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h112
  have h113 := congrArg (fun p : K[X] => p.coeff 3) (h1 1)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h113
  have h114 := congrArg (fun p : K[X] => p.coeff 4) (h1 1)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h114
  have h115 := congrArg (fun p : K[X] => p.coeff 5) (h1 1)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h115
  have h116 := congrArg (fun p : K[X] => p.coeff 6) (h1 1)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h116
  have h120 := congrArg (fun p : K[X] => p.coeff 0) (h2 1)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h120
  have h121 := congrArg (fun p : K[X] => p.coeff 1) (h2 1)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h121
  have h122 := congrArg (fun p : K[X] => p.coeff 2) (h2 1)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h122
  have h123 := congrArg (fun p : K[X] => p.coeff 3) (h2 1)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h123
  have h124 := congrArg (fun p : K[X] => p.coeff 4) (h2 1)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h124
  have h125 := congrArg (fun p : K[X] => p.coeff 5) (h2 1)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h125
  have h126 := congrArg (fun p : K[X] => p.coeff 6) (h2 1)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h126
  have h127 := congrArg (fun p : K[X] => p.coeff 7) (h2 1)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h127
  have h200 := congrArg (fun p : K[X] => p.coeff 0) (h0 2)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h200
  have h201 := congrArg (fun p : K[X] => p.coeff 1) (h0 2)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h201
  have h202 := congrArg (fun p : K[X] => p.coeff 2) (h0 2)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h202
  have h203 := congrArg (fun p : K[X] => p.coeff 3) (h0 2)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h203
  have h204 := congrArg (fun p : K[X] => p.coeff 4) (h0 2)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h204
  have h205 := congrArg (fun p : K[X] => p.coeff 5) (h0 2)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h205
  have h210 := congrArg (fun p : K[X] => p.coeff 0) (h1 2)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h210
  have h211 := congrArg (fun p : K[X] => p.coeff 1) (h1 2)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h211
  have h212 := congrArg (fun p : K[X] => p.coeff 2) (h1 2)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h212
  have h213 := congrArg (fun p : K[X] => p.coeff 3) (h1 2)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h213
  have h214 := congrArg (fun p : K[X] => p.coeff 4) (h1 2)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h214
  have h215 := congrArg (fun p : K[X] => p.coeff 5) (h1 2)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h215
  have h220 := congrArg (fun p : K[X] => p.coeff 0) (h2 2)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h220
  have h221 := congrArg (fun p : K[X] => p.coeff 1) (h2 2)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h221
  have h222 := congrArg (fun p : K[X] => p.coeff 2) (h2 2)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h222
  have h223 := congrArg (fun p : K[X] => p.coeff 3) (h2 2)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h223
  have h224 := congrArg (fun p : K[X] => p.coeff 4) (h2 2)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h224
  have h225 := congrArg (fun p : K[X] => p.coeff 5) (h2 2)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h225
  have h226 := congrArg (fun p : K[X] => p.coeff 6) (h2 2)
  norm_num [hn02,hn12,Ne.symm hn02,Ne.symm hn12,coeff_add,coeff_sub,
    coeff_mul_X_pow',coeff_mul_X,hcE] at h226
  have hz0 (j : Fin 7) (d : Fin 3) : (E 0 j).coeff d.val = 0 := by
    fin_cases j <;> fin_cases d
    · change (E 0 0).coeff 0 = 0
      linear_combination h000 + h100 + h101 - h103 - h110 + h112 - h114 - h116 + h123 + 2*h124 + h126 + h202 - 2*h203 - h210 + h212 + h214 - h222 + h224 + h226
    · change (E 0 0).coeff 1 = 0
      linear_combination h003 - h024 - h200 + h202 - h223
    · change (E 0 0).coeff 2 = 0
      linear_combination - h000 + h002 - h023 - h100 - h101 + h103 + h110 - h112 + h114 + h116 - h123 - 2*h124 - h126 - h202 + h203 + h210 - h212 - h224 - h226
    · change (E 0 1).coeff 0 = 0
      linear_combination h010
    · change (E 0 1).coeff 1 = 0
      linear_combination - 2*h000 + h002 + h010 + h011 - h012 + h014 - h015 + h016 - h023 - h024 + h025 - h026 - 2*h100 - 2*h101 + 2*h103 + 2*h110 - 2*h112 + 2*h114 + 2*h116 - 2*h123 - 4*h124 - 2*h126 - 2*h202 + 3*h203 + 2*h210 - 2*h212 - h214 + h222 - 2*h224 - 2*h226
    · change (E 0 1).coeff 2 = 0
      linear_combination - 2*h000 + 2*h002 - h003 + h011 - h013 + h014 - h015 - h023 + h025 - h027 - 2*h100 - 2*h101 + 2*h103 + 2*h110 - 2*h112 + 2*h114 + 2*h116 - 2*h123 - 4*h124 - 2*h126 + h200 - 3*h202 + 2*h203 + 2*h210 - 2*h212 + h223 - 2*h224 - 2*h226
    · change (E 0 2).coeff 0 = 0
      linear_combination h020
    · change (E 0 2).coeff 1 = 0
      linear_combination h021
    · change (E 0 2).coeff 2 = 0
      linear_combination h000 - h010 + h012 - h014 - h016 + h022 + h023 + h024 + h026 + h100 + h101 - h103 - h110 + h112 - h114 - h116 + h123 + 2*h124 + h126 + h202 - 2*h203 - h210 + h212 + h214 - h222 + h224 + h226
    · change (E 0 3).coeff 0 = 0
      linear_combination h000 + h004 - h015 + h023 + h100 + h101 - h103 - h110 + h112 - h114 - h116 + h123 + 2*h124 + h126 - h201 + h202 - 2*h203 - h210 + h212 + 2*h214 - h222 + h226
    · change (E 0 3).coeff 1 = 0
      linear_combination - 3*h000 + 2*h002 + h005 + h010 + h011 - h012 - h013 + h014 - h015 - 2*h023 - h024 + h025 - h026 - h027 - 3*h100 - 3*h101 + 3*h103 + 3*h110 - 3*h112 + 3*h114 + 3*h116 - 3*h123 - 6*h124 - 3*h126 + h200 - 4*h202 + 5*h203 + 3*h210 - h211 - 3*h212 + h213 - 2*h214 + h215 + h222 - 3*h224 - h225 - 3*h226
    · change (E 0 3).coeff 2 = 0
      linear_combination h006 + h201 - h202 + h203 + h210 - h212 - h214 - h226
    · change (E 0 4).coeff 0 = 0
      linear_combination - h000 + h010 - h012 + h014 + h016 - h023 - h024 - h026 - h100 - h101 + h103 + h110 - h112 + h114 + h116 - h123 - 2*h124 - h126 - h202 + 2*h203 + h210 - h212 - h214 + h222 - h224 - h226
    · change (E 0 4).coeff 1 = 0
      linear_combination h000 + h023 + h100 + h101 - h103 - h110 + h112 - h114 - h116 + h123 + 2*h124 + h126 + h202 - 2*h203 - h210 + h212 + h214 - h222 + h224 + h226
    · change (E 0 4).coeff 2 = 0
      linear_combination - 3*h000 + 2*h002 + h010 + h011 - h012 - h013 + h014 - h015 + h016 - 2*h023 - h024 + h025 - h026 - h027 - 3*h100 - 3*h101 + 3*h103 + 3*h110 - 3*h112 + 3*h114 + 3*h116 - 3*h123 - 6*h124 - 3*h126 - 3*h202 + 4*h203 + 3*h210 - 3*h212 - h214 + h222 - 3*h224 - 3*h226
    · change (E 0 5).coeff 0 = 0
      linear_combination 3*h000 - 2*h002 + h003 - h010 - h011 + h012 + h013 - h014 + h015 - h016 + 2*h023 + h024 - h025 + h026 + h027 + 3*h100 + 3*h101 - 3*h103 - 3*h110 + 3*h112 - 3*h114 - 3*h116 + 3*h123 + 6*h124 + 3*h126 - h200 + 4*h202 - 4*h203 - 3*h210 + 3*h212 + h214 - h222 - h223 + 3*h224 + 3*h226
    · change (E 0 5).coeff 1 = 0
      linear_combination - h000 + h015 - h023 - h100 - h101 + h103 + h110 - h112 + h114 + h116 - h123 - 2*h124 - h126 - h202 + 2*h203 + h210 - h212 - h214 + h222 - h224 - h226
    · change (E 0 5).coeff 2 = 0
      linear_combination 3*h000 - 2*h002 - h010 - h011 + h012 + h013 - h014 + h015 + 2*h023 + h024 - h025 + h026 + h027 + 3*h100 + 3*h101 - 3*h103 - 3*h110 + 3*h112 - 3*h114 - 3*h116 + 3*h123 + 6*h124 + 3*h126 + 3*h202 - 4*h203 - 3*h210 + 3*h212 + h214 - h222 + 3*h224 + 3*h226
    · change (E 0 6).coeff 0 = 0
      linear_combination h002 - h015 + h025 - h203 + h214 - h222
    · change (E 0 6).coeff 1 = 0
      linear_combination - 3*h000 + 2*h002 + h010 + h011 - h012 - h013 + h014 - h015 - 2*h023 - h024 + h025 - h027 - 3*h100 - 3*h101 + 3*h103 + 3*h110 - 3*h112 + 3*h114 + 3*h116 - 3*h123 - 6*h124 - 3*h126 - 3*h202 + 4*h203 + 3*h210 - 3*h212 - h214 + h222 - 3*h224 - 3*h226
    · change (E 0 6).coeff 2 = 0
      linear_combination h027
  have hz1 (j : Fin 7) (d : Fin 3) : (E 1 j).coeff d.val = 0 := by
    fin_cases j <;> fin_cases d
    · change (E 1 0).coeff 0 = 0
      linear_combination h100
    · change (E 1 0).coeff 1 = 0
      linear_combination h103 - h124
    · change (E 1 0).coeff 2 = 0
      linear_combination - h100 + h102 - h123
    · change (E 1 1).coeff 0 = 0
      linear_combination h100 + h101 - h103 + h112 - h114 - h116 + h123 + 2*h124 + h126 + h202 - 2*h203 - h210 + h212 + h214 - h222 + h224 + h226
    · change (E 1 1).coeff 1 = 0
      linear_combination - h000 - h001 + h003 + h010 - h012 + h014 + h016 - h023 - 2*h024 - h026 - 2*h100 + h102 + h110 + h111 - h112 + h114 - h115 + h116 - h123 - h124 + h125 - h126 - 2*h200 + h202 + h203 + h210 + h211 - h212 - h213 - h215 + h222 - h223 - h224 + h225 - h226
    · change (E 1 1).coeff 2 = 0
      linear_combination - h000 - h001 + h003 + h010 - h012 + h014 + h016 - h023 - 2*h024 - h026 - 3*h100 - h101 + 2*h102 + h110 + h111 - h112 - h113 + 2*h114 - h115 + h116 - 2*h123 - 2*h124 + h125 - h126 - h127 - h200 - h201 + h203 + h210 + h211 - h212 - h213 + h214 - h215 + h222 - 2*h224 + h225 - h226
    · change (E 1 2).coeff 0 = 0
      linear_combination h120
    · change (E 1 2).coeff 1 = 0
      linear_combination h121
    · change (E 1 2).coeff 2 = 0
      linear_combination - h101 + h103 + h122 - h124
    · change (E 1 3).coeff 0 = 0
      linear_combination h100 + h104 - h115 + h123 - h200 + h202 - h203 + h211 - h213 + h214 - h215 + h225
    · change (E 1 3).coeff 1 = 0
      linear_combination - h000 - h001 + h003 + h010 - h012 + h014 + h016 - h023 - 2*h024 - h026 - 3*h100 + 2*h102 + h105 + h110 + h111 - h112 - h113 + h114 - h115 - 2*h123 - h124 + h125 - h126 - h127 - h200 - h201 + h202 + h211 - h213 + h214 - h215 + h222 - h224 + h225
    · change (E 1 3).coeff 2 = 0
      linear_combination h106
    · change (E 1 4).coeff 0 = 0
      linear_combination h101 - h103 + h124
    · change (E 1 4).coeff 1 = 0
      linear_combination h100 + h123
    · change (E 1 4).coeff 2 = 0
      linear_combination - h000 - h001 + h003 + h010 - h012 + h014 + h016 - h023 - 2*h024 - h026 - 3*h100 + 2*h102 + h110 + h111 - h112 - h113 + h114 - h115 + h116 - 2*h123 - h124 + h125 - h126 - h127 - h200 + h203 + h210 + h211 - h212 - h213 - h215 + h222 - h224 + h225 - h226
    · change (E 1 5).coeff 0 = 0
      linear_combination h000 + h001 - h003 - h010 + h012 - h014 - h016 + h023 + 2*h024 + h026 + 3*h100 - 2*h102 + h103 - h110 - h111 + h112 + h113 - h114 + h115 - h116 + 2*h123 + h124 - h125 + h126 + h127 + h200 - h203 - h210 - h211 + h212 + h213 + h215 - h222 + h224 - h225 + h226
    · change (E 1 5).coeff 1 = 0
      linear_combination - h100 + h115 - h123 + h200 - h202 + h203 - h211 + h213 - h214 + h215 - h225
    · change (E 1 5).coeff 2 = 0
      linear_combination h000 + h001 - h003 - h010 + h012 - h014 - h016 + h023 + 2*h024 + h026 + 3*h100 - 2*h102 - h110 - h111 + h112 + h113 - h114 + h115 + 2*h123 + h124 - h125 + h126 + h127 + h200 + h201 - h202 - h211 + h213 - h214 + h215 - h222 + h224 - h225
    · change (E 1 6).coeff 0 = 0
      linear_combination h102 - h115 + h125 - h200 + h202 - h203 + h211 - h213 + h214 - h215 + h225
    · change (E 1 6).coeff 1 = 0
      linear_combination - h000 - h001 + h003 + h010 - h012 + h014 + h016 - h023 - 2*h024 - h026 - 3*h100 + 2*h102 + h110 + h111 - h112 - h113 + h114 - h115 - 2*h123 - h124 + h125 - h127 - h200 - h201 + h202 + h211 - h213 + h214 - h215 + h222 - h224 + h225
    · change (E 1 6).coeff 2 = 0
      linear_combination h127
  have hz2 (j : Fin 7) (d : Fin 2) : (E 2 j).coeff d.val = 0 := by
    fin_cases j <;> fin_cases d
    · change (E 2 0).coeff 0 = 0
      linear_combination h200
    · change (E 2 0).coeff 1 = 0
      linear_combination h201 + h203 - h214
    · change (E 2 1).coeff 0 = 0
      linear_combination h210
    · change (E 2 1).coeff 1 = 0
      linear_combination h213
    · change (E 2 2).coeff 0 = 0
      linear_combination h100 + h101 - h103 - h110 + h112 - h114 - h116 + h123 + 2*h124 + h126 + h202 - 2*h203 - h210 + h212 + h214 + h220 - h222 + h224 + h226
    · change (E 2 2).coeff 1 = 0
      linear_combination - h000 - h001 + h003 + h010 - h012 + h014 + h016 - h023 - 2*h024 - h026 - h100 - h101 + h103 + h110 - h112 + h114 + h116 - h123 - 2*h124 - h126 - h200 + 2*h203 + h210 - h212 - h214 + h221 + h222 - h223 - h224 - h226
    · change (E 2 3).coeff 0 = 0
      linear_combination h202 + h204 - h215
    · change (E 2 3).coeff 1 = 0
      linear_combination h205
    · change (E 2 4).coeff 0 = 0
      linear_combination - h203 + h214
    · change (E 2 4).coeff 1 = 0
      linear_combination h202
    · change (E 2 5).coeff 0 = 0
      linear_combination h203
    · change (E 2 5).coeff 1 = 0
      linear_combination - h202 + h215
    · change (E 2 6).coeff 0 = 0
      linear_combination h200 + h203 - h211 + h213 - h214
    · change (E 2 6).coeff 1 = 0
      linear_combination h201 - h202 + h203 + h210 - h212 - h214
  have hzero : E = 0 := by
    funext i j
    apply Polynomial.ext
    intro d
    fin_cases i
    · by_cases hd : d < 3
      · exact (hz0 j ⟨d,hd⟩).trans (coeff_zero _).symm
      · simpa using hcE 0 j d (by simpa [hn02,hn12] using (show 2 < d by omega))
    · by_cases hd : d < 3
      · exact (hz1 j ⟨d,hd⟩).trans (coeff_zero _).symm
      · simpa using hcE 1 j d (by simpa [hn02,hn12] using (show 2 < d by omega))
    · by_cases hd : d < 2
      · exact (hz2 j ⟨d,hd⟩).trans (coeff_zero _).symm
      · simpa using hcE 2 j d (by simpa [hn02,hn12] using (show 1 < d by omega))
  refine ⟨hzero,?_⟩
  have h := congrArg (fun A : Matrix (Fin 3) (Fin 3) K[X] => A 0 0) hrel
  simpa [hzero] using h.symm

end FD56
