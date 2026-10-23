/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.UniformThreeWitness

/-! A sparse two-block witness on three coordinates. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K : Type*} [Field K]

def uniformTwoCoreWitness : Matrix (Fin 6) (Fin 3) K[X] :=
  ![![1, X, -X^3], ![0, 1, 0], ![0, 0, 1],
    ![X^4, 0, 0], ![0, X^4, X^2], ![X^3, 0, X^4]]

theorem uniformTwoCoreWitness_degree : DegreeBound (uniformTwoCoreWitness (K := K)) 4 := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [uniformTwoCoreWitness]

theorem uniformTwoCoreWitness_injective :
    Function.Injective (uniformTwoCoreWitness (K := K)).mulVec := by
  apply polynomial_matrix_injective_of_zero
  intro u v h
  funext j
  fin_cases j
  · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, uniformTwoCoreWitness]
      using congrFun h (0 : Fin 6)
  · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, uniformTwoCoreWitness]
      using congrFun h (1 : Fin 6)
  · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, uniformTwoCoreWitness]
      using congrFun h (2 : Fin 6)

set_option maxHeartbeats 2000000 in
theorem uniformTwoCoreWitness_scalar_obstruction
    (E : Matrix (Fin 3) (Fin 6) K[X]) (c : K[X]) (hE : DegreeBound E 2)
    (hrel : E * uniformTwoCoreWitness = (-c) • (1 : Matrix (Fin 3) (Fin 3) K[X])) :
    E = 0 ∧ c = 0 := by
  have hn02 : (0 : Fin 3) ≠ 2 := by decide
  have hn12 : (1 : Fin 3) ≠ 2 := by decide
  have hcE (i : Fin 3) (j : Fin 6) (d : ℕ) (hd : 2 < d) : (E i j).coeff d = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hE i j) hd)
  have hentry (i j : Fin 3) :
      (E * uniformTwoCoreWitness (K := K)) i j + (if i = j then c else 0) = 0 := by
    have h := congrArg (fun A : Matrix (Fin 3) (Fin 3) K[X] => A i j) hrel
    by_cases hij : i = j <;> simp [hij, Matrix.smul_apply, Matrix.one_apply] at h ⊢ <;>
      linear_combination h
  have h0 (i : Fin 3) :
      E i 0 + E i 3 * X^4 + E i 5 * X^3 + (if i = 0 then c else 0) = 0 := by
    simpa [uniformTwoCoreWitness, Matrix.mul_apply, Fin.sum_univ_succ, add_assoc]
      using hentry i 0
  have h1 (i : Fin 3) :
      E i 0 * X + E i 1 + E i 4 * X^4 + (if i = 1 then c else 0) = 0 := by
    simpa [uniformTwoCoreWitness, Matrix.mul_apply, Fin.sum_univ_succ, add_assoc]
      using hentry i 1
  have h2 (i : Fin 3) :
      -(E i 0 * X^3) + E i 2 + E i 4 * X^2 + E i 5 * X^4 +
        (if i = 2 then c else 0) = 0 := by
    simpa [uniformTwoCoreWitness, Matrix.mul_apply, Fin.sum_univ_succ, add_assoc]
      using hentry i 2
  have h000 := congrArg (fun p : K[X] => p.coeff 0) (h0 0)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h000
  have h001 := congrArg (fun p : K[X] => p.coeff 1) (h0 0)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h001
  have h002 := congrArg (fun p : K[X] => p.coeff 2) (h0 0)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h002
  have h003 := congrArg (fun p : K[X] => p.coeff 3) (h0 0)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h003
  have h004 := congrArg (fun p : K[X] => p.coeff 4) (h0 0)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h004
  have h005 := congrArg (fun p : K[X] => p.coeff 5) (h0 0)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h005
  have h006 := congrArg (fun p : K[X] => p.coeff 6) (h0 0)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h006
  have h010 := congrArg (fun p : K[X] => p.coeff 0) (h1 0)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h010
  have h011 := congrArg (fun p : K[X] => p.coeff 1) (h1 0)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h011
  have h012 := congrArg (fun p : K[X] => p.coeff 2) (h1 0)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h012
  have h013 := congrArg (fun p : K[X] => p.coeff 3) (h1 0)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h013
  have h014 := congrArg (fun p : K[X] => p.coeff 4) (h1 0)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h014
  have h015 := congrArg (fun p : K[X] => p.coeff 5) (h1 0)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h015
  have h016 := congrArg (fun p : K[X] => p.coeff 6) (h1 0)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h016
  have h020 := congrArg (fun p : K[X] => p.coeff 0) (h2 0)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h020
  have h021 := congrArg (fun p : K[X] => p.coeff 1) (h2 0)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h021
  have h022 := congrArg (fun p : K[X] => p.coeff 2) (h2 0)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h022
  have h023 := congrArg (fun p : K[X] => p.coeff 3) (h2 0)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h023
  have h024 := congrArg (fun p : K[X] => p.coeff 4) (h2 0)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h024
  have h025 := congrArg (fun p : K[X] => p.coeff 5) (h2 0)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h025
  have h026 := congrArg (fun p : K[X] => p.coeff 6) (h2 0)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h026
  have h100 := congrArg (fun p : K[X] => p.coeff 0) (h0 1)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h100
  have h101 := congrArg (fun p : K[X] => p.coeff 1) (h0 1)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h101
  have h102 := congrArg (fun p : K[X] => p.coeff 2) (h0 1)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h102
  have h103 := congrArg (fun p : K[X] => p.coeff 3) (h0 1)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h103
  have h104 := congrArg (fun p : K[X] => p.coeff 4) (h0 1)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h104
  have h105 := congrArg (fun p : K[X] => p.coeff 5) (h0 1)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h105
  have h106 := congrArg (fun p : K[X] => p.coeff 6) (h0 1)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h106
  have h110 := congrArg (fun p : K[X] => p.coeff 0) (h1 1)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h110
  have h111 := congrArg (fun p : K[X] => p.coeff 1) (h1 1)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h111
  have h112 := congrArg (fun p : K[X] => p.coeff 2) (h1 1)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h112
  have h113 := congrArg (fun p : K[X] => p.coeff 3) (h1 1)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h113
  have h114 := congrArg (fun p : K[X] => p.coeff 4) (h1 1)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h114
  have h115 := congrArg (fun p : K[X] => p.coeff 5) (h1 1)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h115
  have h116 := congrArg (fun p : K[X] => p.coeff 6) (h1 1)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h116
  have h120 := congrArg (fun p : K[X] => p.coeff 0) (h2 1)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h120
  have h121 := congrArg (fun p : K[X] => p.coeff 1) (h2 1)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h121
  have h122 := congrArg (fun p : K[X] => p.coeff 2) (h2 1)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h122
  have h123 := congrArg (fun p : K[X] => p.coeff 3) (h2 1)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h123
  have h124 := congrArg (fun p : K[X] => p.coeff 4) (h2 1)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h124
  have h125 := congrArg (fun p : K[X] => p.coeff 5) (h2 1)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h125
  have h126 := congrArg (fun p : K[X] => p.coeff 6) (h2 1)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h126
  have h200 := congrArg (fun p : K[X] => p.coeff 0) (h0 2)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h200
  have h201 := congrArg (fun p : K[X] => p.coeff 1) (h0 2)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h201
  have h202 := congrArg (fun p : K[X] => p.coeff 2) (h0 2)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h202
  have h203 := congrArg (fun p : K[X] => p.coeff 3) (h0 2)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h203
  have h204 := congrArg (fun p : K[X] => p.coeff 4) (h0 2)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h204
  have h205 := congrArg (fun p : K[X] => p.coeff 5) (h0 2)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h205
  have h206 := congrArg (fun p : K[X] => p.coeff 6) (h0 2)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h206
  have h210 := congrArg (fun p : K[X] => p.coeff 0) (h1 2)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h210
  have h211 := congrArg (fun p : K[X] => p.coeff 1) (h1 2)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h211
  have h212 := congrArg (fun p : K[X] => p.coeff 2) (h1 2)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h212
  have h213 := congrArg (fun p : K[X] => p.coeff 3) (h1 2)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h213
  have h214 := congrArg (fun p : K[X] => p.coeff 4) (h1 2)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h214
  have h215 := congrArg (fun p : K[X] => p.coeff 5) (h1 2)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h215
  have h216 := congrArg (fun p : K[X] => p.coeff 6) (h1 2)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h216
  have h220 := congrArg (fun p : K[X] => p.coeff 0) (h2 2)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h220
  have h221 := congrArg (fun p : K[X] => p.coeff 1) (h2 2)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h221
  have h222 := congrArg (fun p : K[X] => p.coeff 2) (h2 2)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h222
  have h223 := congrArg (fun p : K[X] => p.coeff 3) (h2 2)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h223
  have h224 := congrArg (fun p : K[X] => p.coeff 4) (h2 2)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h224
  have h225 := congrArg (fun p : K[X] => p.coeff 5) (h2 2)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h225
  have h226 := congrArg (fun p : K[X] => p.coeff 6) (h2 2)
  norm_num [hn02, hn12, Ne.symm hn02, Ne.symm hn12, coeff_add,
    coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h226
  have hz (i : Fin 3) (j : Fin 6) (d : Fin 3) : (E i j).coeff d.val = 0 := by
    fin_cases i <;> fin_cases j <;> fin_cases d
    · change (E 0 0).coeff 0 = 0
      linear_combination h015 - h023
    · change (E 0 0).coeff 1 = 0
      linear_combination h003 + h016 - h024 + h102 - h113
    · change (E 0 0).coeff 2 = 0
      linear_combination h013
    · change (E 0 1).coeff 0 = 0
      linear_combination h010
    · change (E 0 1).coeff 1 = 0
      linear_combination h011 - h015 + h023
    · change (E 0 1).coeff 2 = 0
      linear_combination - h003 + h012 - h016 + h024 - h102 + h113
    · change (E 0 2).coeff 0 = 0
      linear_combination h020
    · change (E 0 2).coeff 1 = 0
      linear_combination h021
    · change (E 0 2).coeff 2 = 0
      linear_combination - h014 + h022
    · change (E 0 3).coeff 0 = 0
      linear_combination h004 - h013 - h025 - h201 + h203 + h216 - h224
    · change (E 0 3).coeff 1 = 0
      linear_combination h005 - h026 + h100 - h115 + h123
    · change (E 0 3).coeff 2 = 0
      linear_combination h006 + h101 - h103 - h116 + h124
    · change (E 0 4).coeff 0 = 0
      linear_combination h014
    · change (E 0 4).coeff 1 = 0
      linear_combination h015
    · change (E 0 4).coeff 2 = 0
      linear_combination h016
    · change (E 0 5).coeff 0 = 0
      linear_combination h003 + h102 - h113
    · change (E 0 5).coeff 1 = 0
      linear_combination h013 + h025
    · change (E 0 5).coeff 2 = 0
      linear_combination h026
    · change (E 1 0).coeff 0 = 0
      linear_combination h100
    · change (E 1 0).coeff 1 = 0
      linear_combination h101
    · change (E 1 0).coeff 2 = 0
      linear_combination h102
    · change (E 1 1).coeff 0 = 0
      linear_combination - h000 + h015 - h023 + h110
    · change (E 1 1).coeff 1 = 0
      linear_combination - h001 + h003 + h016 - h024 - h100 + h102 + h111 - h113
    · change (E 1 1).coeff 2 = 0
      linear_combination - h002 + h013 - h101 + h112
    · change (E 1 2).coeff 0 = 0
      linear_combination h120
    · change (E 1 2).coeff 1 = 0
      linear_combination h121
    · change (E 1 2).coeff 2 = 0
      linear_combination - h114 + h122 + h201 - h203 - h216 + h224
    · change (E 1 3).coeff 0 = 0
      linear_combination - h102 + h104 - h125
    · change (E 1 3).coeff 1 = 0
      linear_combination h105 - h126
    · change (E 1 3).coeff 2 = 0
      linear_combination h106
    · change (E 1 4).coeff 0 = 0
      linear_combination h114 - h201 + h203 + h216 - h224
    · change (E 1 4).coeff 1 = 0
      linear_combination h100 + h123
    · change (E 1 4).coeff 2 = 0
      linear_combination h101 - h103 + h124
    · change (E 1 5).coeff 0 = 0
      linear_combination h103
    · change (E 1 5).coeff 1 = 0
      linear_combination h102 + h125
    · change (E 1 5).coeff 2 = 0
      linear_combination h126
    · change (E 2 0).coeff 0 = 0
      linear_combination h200
    · change (E 2 0).coeff 1 = 0
      linear_combination h201
    · change (E 2 0).coeff 2 = 0
      linear_combination h202
    · change (E 2 1).coeff 0 = 0
      linear_combination h210
    · change (E 2 1).coeff 1 = 0
      linear_combination - h200 + h211
    · change (E 2 1).coeff 2 = 0
      linear_combination - h201 + h212
    · change (E 2 2).coeff 0 = 0
      linear_combination - h000 + h015 - h023 + h220
    · change (E 2 2).coeff 1 = 0
      linear_combination - h001 + h003 + h016 - h024 + h102 - h113 + h221
    · change (E 2 2).coeff 2 = 0
      linear_combination - h002 + h013 - h214 + h222
    · change (E 2 3).coeff 0 = 0
      linear_combination - h100 + h115 - h123 - h202 + h204 - h225
    · change (E 2 3).coeff 1 = 0
      linear_combination - h101 + h103 + h116 - h124 + h205 - h226
    · change (E 2 3).coeff 2 = 0
      linear_combination h206
    · change (E 2 4).coeff 0 = 0
      linear_combination h214
    · change (E 2 4).coeff 1 = 0
      linear_combination h215
    · change (E 2 4).coeff 2 = 0
      linear_combination h216
    · change (E 2 5).coeff 0 = 0
      linear_combination h203
    · change (E 2 5).coeff 1 = 0
      linear_combination h100 - h115 + h123 + h202 + h225
    · change (E 2 5).coeff 2 = 0
      linear_combination h101 - h103 - h116 + h124 + h226
  have hzero : E = 0 := by
    funext i j
    apply Polynomial.ext
    intro d
    by_cases hd : d < 3
    · exact (hz i j ⟨d,hd⟩).trans (coeff_zero _).symm
    · simpa using hcE i j d (by omega)
  refine ⟨hzero,?_⟩
  have h := congrArg (fun A : Matrix (Fin 3) (Fin 3) K[X] => A 0 0) hrel
  simpa [hzero] using h.symm

end FD56
