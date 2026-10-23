/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.UniformThreeWitness

/-! A two-coordinate witness for both remaining bounded degrees. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K : Type*} [Field K]

def uniformTwoSmallWitness : Matrix (Fin 4) (Fin 2) K[X] :=
  ![![1, 0], ![-X^2, 1], ![X^4, X], ![0, X^4]]

theorem uniformTwoSmallWitness_degree : DegreeBound (uniformTwoSmallWitness (K := K)) 4 := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [uniformTwoSmallWitness]

theorem uniformTwoSmallWitness_injective :
    Function.Injective (uniformTwoSmallWitness (K := K)).mulVec := by
  apply polynomial_matrix_injective_of_zero
  intro u v h
  funext j
  fin_cases j
  · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, uniformTwoSmallWitness]
      using congrFun h (0 : Fin 4)
  · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, uniformTwoSmallWitness]
      using congrFun h (1 : Fin 4)

set_option maxHeartbeats 1000000 in
theorem uniformTwoSmallWitness_affine_obstruction
    (E : Matrix (Fin 2) (Fin 4) K[X]) (c : K[X]) (hE : DegreeBound E 1)
    (hrel : E * uniformTwoSmallWitness = (-c) • (1 : Matrix (Fin 2) (Fin 2) K[X]))
    : E = 0 ∧ c = 0 := by
  have hcE (i : Fin 2) (j : Fin 4) (d : ℕ) (hd : 1 < d) : (E i j).coeff d = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hE i j) hd)
  have hentry (i j : Fin 2) :
      (E * uniformTwoSmallWitness (K := K)) i j + (if i = j then c else 0) = 0 := by
    have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) K[X] => A i j) hrel
    by_cases hij : i = j <;> simp [hij, Matrix.smul_apply, Matrix.one_apply] at h ⊢ <;>
      linear_combination h
  have h0 (i : Fin 2) :
      E i 0 - E i 1 * X^2 + E i 2 * X^4 + (if i = 0 then c else 0) = 0 := by
    simpa [uniformTwoSmallWitness, Matrix.mul_apply, Fin.sum_univ_succ, add_assoc, sub_eq_add_neg]
      using hentry i 0
  have h1 (i : Fin 2) :
      E i 1 + E i 2 * X + E i 3 * X^4 + (if i = 1 then c else 0) = 0 := by
    simpa [uniformTwoSmallWitness, Matrix.mul_apply, Fin.sum_univ_succ, add_assoc]
      using hentry i 1
  have h000 := congrArg (fun p : K[X] => p.coeff 0) (h0 0)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h000
  have h001 := congrArg (fun p : K[X] => p.coeff 1) (h0 0)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h001
  have h002 := congrArg (fun p : K[X] => p.coeff 2) (h0 0)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h002
  have h003 := congrArg (fun p : K[X] => p.coeff 3) (h0 0)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h003
  have h004 := congrArg (fun p : K[X] => p.coeff 4) (h0 0)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h004
  have h005 := congrArg (fun p : K[X] => p.coeff 5) (h0 0)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h005
  have h010 := congrArg (fun p : K[X] => p.coeff 0) (h1 0)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h010
  have h011 := congrArg (fun p : K[X] => p.coeff 1) (h1 0)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h011
  have h012 := congrArg (fun p : K[X] => p.coeff 2) (h1 0)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h012
  have h013 := congrArg (fun p : K[X] => p.coeff 3) (h1 0)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h013
  have h014 := congrArg (fun p : K[X] => p.coeff 4) (h1 0)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h014
  have h015 := congrArg (fun p : K[X] => p.coeff 5) (h1 0)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h015
  have h100 := congrArg (fun p : K[X] => p.coeff 0) (h0 1)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h100
  have h101 := congrArg (fun p : K[X] => p.coeff 1) (h0 1)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h101
  have h102 := congrArg (fun p : K[X] => p.coeff 2) (h0 1)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h102
  have h103 := congrArg (fun p : K[X] => p.coeff 3) (h0 1)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h103
  have h104 := congrArg (fun p : K[X] => p.coeff 4) (h0 1)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h104
  have h105 := congrArg (fun p : K[X] => p.coeff 5) (h0 1)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h105
  have h110 := congrArg (fun p : K[X] => p.coeff 0) (h1 1)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h110
  have h111 := congrArg (fun p : K[X] => p.coeff 1) (h1 1)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h111
  have h112 := congrArg (fun p : K[X] => p.coeff 2) (h1 1)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h112
  have h113 := congrArg (fun p : K[X] => p.coeff 3) (h1 1)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h113
  have h114 := congrArg (fun p : K[X] => p.coeff 4) (h1 1)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h114
  have h115 := congrArg (fun p : K[X] => p.coeff 5) (h1 1)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h115
  have hz (i : Fin 2) (j : Fin 4) (d : Fin 2) : (E i j).coeff d.val = 0 := by
    fin_cases i <;> fin_cases j <;> fin_cases d
    · change (E 0 0).coeff 0 = 0
      linear_combination h000 + h102 - h110
    · change (E 0 0).coeff 1 = 0
      linear_combination h001 + h103 + h104 - h111
    · change (E 0 1).coeff 0 = 0
      linear_combination h010
    · change (E 0 1).coeff 1 = 0
      linear_combination - h003 + h113
    · change (E 0 2).coeff 0 = 0
      linear_combination h003 + h011 - h113
    · change (E 0 2).coeff 1 = 0
      linear_combination h012
    · change (E 0 3).coeff 0 = 0
      linear_combination h014
    · change (E 0 3).coeff 1 = 0
      linear_combination h015
    · change (E 1 0).coeff 0 = 0
      linear_combination h100
    · change (E 1 0).coeff 1 = 0
      linear_combination h101
    · change (E 1 1).coeff 0 = 0
      linear_combination h102
    · change (E 1 1).coeff 1 = 0
      linear_combination h103
    · change (E 1 2).coeff 0 = 0
      linear_combination h104
    · change (E 1 2).coeff 1 = 0
      linear_combination h105
    · change (E 1 3).coeff 0 = 0
      linear_combination h003 - h004 + h011 - h113 + h114
    · change (E 1 3).coeff 1 = 0
      linear_combination - h005 + h012 + h115
  have hzero : E = 0 := by
    funext i j
    apply Polynomial.ext
    intro d
    by_cases hd : d < 2
    · exact (hz i j ⟨d,hd⟩).trans (coeff_zero _).symm
    · simpa using hcE i j d (by omega)
  refine ⟨hzero,?_⟩
  have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) K[X] => A 0 0) hrel
  simpa [hzero] using h.symm

set_option maxHeartbeats 1000000 in
theorem uniformTwoSmallWitness_quadratic_obstruction
    (E : Matrix (Fin 2) (Fin 4) K[X]) (c : K[X]) (hE : DegreeBound E 2)
    (hrel : E * uniformTwoSmallWitness = (-c) • (1 : Matrix (Fin 2) (Fin 2) K[X]))
    (hc0 : c.coeff 0 = 0) (hc1 : c.coeff 1 = 0) (hc4 : c.coeff 4 = 0)
    : E = 0 ∧ c = 0 := by
  have hcE (i : Fin 2) (j : Fin 4) (d : ℕ) (hd : 2 < d) : (E i j).coeff d = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hE i j) hd)
  have hentry (i j : Fin 2) :
      (E * uniformTwoSmallWitness (K := K)) i j + (if i = j then c else 0) = 0 := by
    have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) K[X] => A i j) hrel
    by_cases hij : i = j <;> simp [hij, Matrix.smul_apply, Matrix.one_apply] at h ⊢ <;>
      linear_combination h
  have h0 (i : Fin 2) :
      E i 0 - E i 1 * X^2 + E i 2 * X^4 + (if i = 0 then c else 0) = 0 := by
    simpa [uniformTwoSmallWitness, Matrix.mul_apply, Fin.sum_univ_succ, add_assoc, sub_eq_add_neg]
      using hentry i 0
  have h1 (i : Fin 2) :
      E i 1 + E i 2 * X + E i 3 * X^4 + (if i = 1 then c else 0) = 0 := by
    simpa [uniformTwoSmallWitness, Matrix.mul_apply, Fin.sum_univ_succ, add_assoc]
      using hentry i 1
  have h000 := congrArg (fun p : K[X] => p.coeff 0) (h0 0)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h000
  have h001 := congrArg (fun p : K[X] => p.coeff 1) (h0 0)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h001
  have h002 := congrArg (fun p : K[X] => p.coeff 2) (h0 0)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h002
  have h003 := congrArg (fun p : K[X] => p.coeff 3) (h0 0)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h003
  have h004 := congrArg (fun p : K[X] => p.coeff 4) (h0 0)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h004
  have h005 := congrArg (fun p : K[X] => p.coeff 5) (h0 0)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h005
  have h006 := congrArg (fun p : K[X] => p.coeff 6) (h0 0)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h006
  have h010 := congrArg (fun p : K[X] => p.coeff 0) (h1 0)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h010
  have h011 := congrArg (fun p : K[X] => p.coeff 1) (h1 0)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h011
  have h012 := congrArg (fun p : K[X] => p.coeff 2) (h1 0)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h012
  have h013 := congrArg (fun p : K[X] => p.coeff 3) (h1 0)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h013
  have h014 := congrArg (fun p : K[X] => p.coeff 4) (h1 0)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h014
  have h015 := congrArg (fun p : K[X] => p.coeff 5) (h1 0)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h015
  have h016 := congrArg (fun p : K[X] => p.coeff 6) (h1 0)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h016
  have h100 := congrArg (fun p : K[X] => p.coeff 0) (h0 1)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h100
  have h101 := congrArg (fun p : K[X] => p.coeff 1) (h0 1)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h101
  have h102 := congrArg (fun p : K[X] => p.coeff 2) (h0 1)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h102
  have h103 := congrArg (fun p : K[X] => p.coeff 3) (h0 1)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h103
  have h104 := congrArg (fun p : K[X] => p.coeff 4) (h0 1)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h104
  have h105 := congrArg (fun p : K[X] => p.coeff 5) (h0 1)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h105
  have h106 := congrArg (fun p : K[X] => p.coeff 6) (h0 1)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h106
  have h110 := congrArg (fun p : K[X] => p.coeff 0) (h1 1)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h110
  have h111 := congrArg (fun p : K[X] => p.coeff 1) (h1 1)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h111
  have h112 := congrArg (fun p : K[X] => p.coeff 2) (h1 1)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h112
  have h113 := congrArg (fun p : K[X] => p.coeff 3) (h1 1)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h113
  have h114 := congrArg (fun p : K[X] => p.coeff 4) (h1 1)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h114
  have h115 := congrArg (fun p : K[X] => p.coeff 5) (h1 1)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h115
  have h116 := congrArg (fun p : K[X] => p.coeff 6) (h1 1)
  norm_num [Fin.reduceEq, coeff_add, coeff_sub, coeff_mul_X_pow', coeff_mul_X, hcE] at h116
  have hz (i : Fin 2) (j : Fin 4) (d : Fin 3) : (E i j).coeff d.val = 0 := by
    fin_cases i <;> fin_cases j <;> fin_cases d
    · change (E 0 0).coeff 0 = 0
      linear_combination h000 - hc0
    · change (E 0 0).coeff 1 = 0
      linear_combination h001 - hc1
    · change (E 0 0).coeff 2 = 0
      linear_combination h002 + h010 - h103 - h104 + h105 + h111 - h112 - hc1
    · change (E 0 1).coeff 0 = 0
      linear_combination h010
    · change (E 0 1).coeff 1 = 0
      linear_combination - h003 - h106 + h113
    · change (E 0 1).coeff 2 = 0
      linear_combination h003 - h004 + h011 + h106 - h113 + hc4
    · change (E 0 2).coeff 0 = 0
      linear_combination h003 + h011 + h106 - h113
    · change (E 0 2).coeff 1 = 0
      linear_combination - h003 + h004 - h011 + h012 - h106 + h113 - hc4
    · change (E 0 2).coeff 2 = 0
      linear_combination h013
    · change (E 0 3).coeff 0 = 0
      linear_combination h014
    · change (E 0 3).coeff 1 = 0
      linear_combination h015
    · change (E 0 3).coeff 2 = 0
      linear_combination h016
    · change (E 1 0).coeff 0 = 0
      linear_combination h100
    · change (E 1 0).coeff 1 = 0
      linear_combination h101
    · change (E 1 0).coeff 2 = 0
      linear_combination h102 + h110 - hc0
    · change (E 1 1).coeff 0 = 0
      linear_combination h110 - hc0
    · change (E 1 1).coeff 1 = 0
      linear_combination h103
    · change (E 1 1).coeff 2 = 0
      linear_combination - h103 - h104 + h111 - hc1
    · change (E 1 2).coeff 0 = 0
      linear_combination - h103 + h111 - hc1
    · change (E 1 2).coeff 1 = 0
      linear_combination h105
    · change (E 1 2).coeff 2 = 0
      linear_combination h106
    · change (E 1 3).coeff 0 = 0
      linear_combination h114 - hc4
    · change (E 1 3).coeff 1 = 0
      linear_combination - h003 + h004 - h005 - h011 + h012 - h106 + h113 + h115 - hc4
    · change (E 1 3).coeff 2 = 0
      linear_combination - h006 + h013 + h116
  have hzero : E = 0 := by
    funext i j
    apply Polynomial.ext
    intro d
    by_cases hd : d < 3
    · exact (hz i j ⟨d,hd⟩).trans (coeff_zero _).symm
    · simpa using hcE i j d (by omega)
  refine ⟨hzero,?_⟩
  have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) K[X] => A 0 0) hrel
  simpa [hzero] using h.symm

end FD56
