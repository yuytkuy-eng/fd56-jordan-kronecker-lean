/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.UniformThreeWitness

/-! A weighted scalar obstruction for the smallest mixed three-block pair. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K : Type*} [Field K]

def mixedThreeSmallWitness : Matrix (Fin 7) (Fin 2) K[X] :=
  ![![1 + X + X^3, 0], ![X^2, 0], ![X^5, 0], ![0, 1],
    ![X^4, X^2], ![X, X^4], ![X^3, X^6]]

theorem mixedThreeSmallWitness_degree (i : Fin 7) (j : Fin 2) :
    (mixedThreeSmallWitness (K := K) i j).natDegree ≤ 5 + j.val := by
  fin_cases i <;> fin_cases j <;> simp [mixedThreeSmallWitness]
  exact (natDegree_add_le _ _).trans (by
    apply max_le
    · exact (natDegree_add_le _ _).trans (by simp)
    · simp)

theorem mixedThreeSmallWitness_injective :
    Function.Injective (mixedThreeSmallWitness (K := K)).mulVec := by
  apply polynomial_matrix_injective_of_zero
  intro u v h
  funext j
  fin_cases j
  · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mixedThreeSmallWitness]
      using congrFun h (0 : Fin 7)
  · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mixedThreeSmallWitness]
      using congrFun h (3 : Fin 7)

set_option maxHeartbeats 2000000 in
theorem mixedThreeSmallWitness_scalar_obstruction
    (E : Matrix (Fin 2) (Fin 7) K[X]) (c : K[X])
    (hE : ∀ i j, (E i j).natDegree ≤ if i = 0 then 1 else 0)
    (hrel : E * mixedThreeSmallWitness = (-c) • (1 : Matrix (Fin 2) (Fin 2) K[X])) :
    E = 0 ∧ c = 0 := by
  have hcE (i : Fin 2) (j : Fin 7) (d : ℕ)
      (hd : (if i = 0 then 1 else 0) < d) : (E i j).coeff d = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hE i j) hd)
  have hentry (i j : Fin 2) :
      (E * mixedThreeSmallWitness (K := K)) i j + (if i = j then c else 0) = 0 := by
    have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) K[X] => A i j) hrel
    by_cases hij : i = j <;> simp [hij, Matrix.smul_apply, Matrix.one_apply] at h ⊢ <;>
      linear_combination h
  have h0 (i : Fin 2) :
      E i 0 * (1 + X + X^3) + E i 1 * X^2 + E i 2 * X^5 +
        E i 4 * X^4 + E i 5 * X + E i 6 * X^3 + (if i = 0 then c else 0) = 0 := by
    simpa [mixedThreeSmallWitness, Matrix.mul_apply, Fin.sum_univ_succ, add_assoc]
      using hentry i 0
  have h1 (i : Fin 2) :
      E i 3 + E i 4 * X^2 + E i 5 * X^4 + E i 6 * X^6 +
        (if i = 1 then c else 0) = 0 := by
    simpa [mixedThreeSmallWitness, Matrix.mul_apply, Fin.sum_univ_succ, add_assoc]
      using hentry i 1
  have h000 := congrArg (fun p : K[X] => p.coeff 0) (h0 0)
  norm_num [mul_add, coeff_add, coeff_mul_X_pow', coeff_mul_X, hcE] at h000
  have h001 := congrArg (fun p : K[X] => p.coeff 1) (h0 0)
  norm_num [mul_add, coeff_add, coeff_mul_X_pow', coeff_mul_X, hcE] at h001
  have h002 := congrArg (fun p : K[X] => p.coeff 2) (h0 0)
  norm_num [mul_add, coeff_add, coeff_mul_X_pow', coeff_mul_X, hcE] at h002
  have h003 := congrArg (fun p : K[X] => p.coeff 3) (h0 0)
  norm_num [mul_add, coeff_add, coeff_mul_X_pow', coeff_mul_X, hcE] at h003
  have h004 := congrArg (fun p : K[X] => p.coeff 4) (h0 0)
  norm_num [mul_add, coeff_add, coeff_mul_X_pow', coeff_mul_X, hcE] at h004
  have h005 := congrArg (fun p : K[X] => p.coeff 5) (h0 0)
  norm_num [mul_add, coeff_add, coeff_mul_X_pow', coeff_mul_X, hcE] at h005
  have h006 := congrArg (fun p : K[X] => p.coeff 6) (h0 0)
  norm_num [mul_add, coeff_add, coeff_mul_X_pow', coeff_mul_X, hcE] at h006
  have h010 := congrArg (fun p : K[X] => p.coeff 0) (h1 0)
  norm_num [mul_add, coeff_add, coeff_mul_X_pow', coeff_mul_X, hcE] at h010
  have h011 := congrArg (fun p : K[X] => p.coeff 1) (h1 0)
  norm_num [mul_add, coeff_add, coeff_mul_X_pow', coeff_mul_X, hcE] at h011
  have h012 := congrArg (fun p : K[X] => p.coeff 2) (h1 0)
  norm_num [mul_add, coeff_add, coeff_mul_X_pow', coeff_mul_X, hcE] at h012
  have h013 := congrArg (fun p : K[X] => p.coeff 3) (h1 0)
  norm_num [mul_add, coeff_add, coeff_mul_X_pow', coeff_mul_X, hcE] at h013
  have h014 := congrArg (fun p : K[X] => p.coeff 4) (h1 0)
  norm_num [mul_add, coeff_add, coeff_mul_X_pow', coeff_mul_X, hcE] at h014
  have h015 := congrArg (fun p : K[X] => p.coeff 5) (h1 0)
  norm_num [mul_add, coeff_add, coeff_mul_X_pow', coeff_mul_X, hcE] at h015
  have h016 := congrArg (fun p : K[X] => p.coeff 6) (h1 0)
  norm_num [mul_add, coeff_add, coeff_mul_X_pow', coeff_mul_X, hcE] at h016
  have h017 := congrArg (fun p : K[X] => p.coeff 7) (h1 0)
  norm_num [mul_add, coeff_add, coeff_mul_X_pow', coeff_mul_X, hcE] at h017
  have h100 := congrArg (fun p : K[X] => p.coeff 0) (h0 1)
  norm_num [mul_add, coeff_add, coeff_mul_X_pow', coeff_mul_X, hcE] at h100
  have h101 := congrArg (fun p : K[X] => p.coeff 1) (h0 1)
  norm_num [mul_add, coeff_add, coeff_mul_X_pow', coeff_mul_X, hcE] at h101
  have h102 := congrArg (fun p : K[X] => p.coeff 2) (h0 1)
  norm_num [mul_add, coeff_add, coeff_mul_X_pow', coeff_mul_X, hcE] at h102
  have h103 := congrArg (fun p : K[X] => p.coeff 3) (h0 1)
  norm_num [mul_add, coeff_add, coeff_mul_X_pow', coeff_mul_X, hcE] at h103
  have h104 := congrArg (fun p : K[X] => p.coeff 4) (h0 1)
  norm_num [mul_add, coeff_add, coeff_mul_X_pow', coeff_mul_X, hcE] at h104
  have h105 := congrArg (fun p : K[X] => p.coeff 5) (h0 1)
  norm_num [mul_add, coeff_add, coeff_mul_X_pow', coeff_mul_X, hcE] at h105
  have h110 := congrArg (fun p : K[X] => p.coeff 0) (h1 1)
  norm_num [mul_add, coeff_add, coeff_mul_X_pow', coeff_mul_X, hcE] at h110
  have h111 := congrArg (fun p : K[X] => p.coeff 1) (h1 1)
  norm_num [mul_add, coeff_add, coeff_mul_X_pow', coeff_mul_X, hcE] at h111
  have h112 := congrArg (fun p : K[X] => p.coeff 2) (h1 1)
  norm_num [mul_add, coeff_add, coeff_mul_X_pow', coeff_mul_X, hcE] at h112
  have h113 := congrArg (fun p : K[X] => p.coeff 3) (h1 1)
  norm_num [mul_add, coeff_add, coeff_mul_X_pow', coeff_mul_X, hcE] at h113
  have h114 := congrArg (fun p : K[X] => p.coeff 4) (h1 1)
  norm_num [mul_add, coeff_add, coeff_mul_X_pow', coeff_mul_X, hcE] at h114
  have h115 := congrArg (fun p : K[X] => p.coeff 5) (h1 1)
  norm_num [mul_add, coeff_add, coeff_mul_X_pow', coeff_mul_X, hcE] at h115
  have h116 := congrArg (fun p : K[X] => p.coeff 6) (h1 1)
  norm_num [mul_add, coeff_add, coeff_mul_X_pow', coeff_mul_X, hcE] at h116
  have hz0 (j : Fin 7) (d : Fin 2) : (E 0 j).coeff d.val = 0 := by
    fin_cases j <;> fin_cases d
    · change (E 0 0).coeff 0 = 0
      linear_combination h001 - h004 + h012 - h014 + h017 + h100 - h101 - h111 + h114
    · change (E 0 0).coeff 1 = 0
      linear_combination h004 - h012 - h017 - h100 + h101 - h114
    · change (E 0 1).coeff 0 = 0
      linear_combination h002 - h004 + h012 - h015 + h017 + h100 - h101 + h104 - h112 + h114
    · change (E 0 1).coeff 1 = 0
      linear_combination - h001 + h003 + h004 - h012 + h014 - h016 - h017 - h100 + h101 + h111 - h113 - h114
    · change (E 0 2).coeff 0 = 0
      linear_combination h005 - h013 - h115
    · change (E 0 2).coeff 1 = 0
      linear_combination h006 - h100 + h103 - h116
    · change (E 0 3).coeff 0 = 0
      linear_combination h010
    · change (E 0 3).coeff 1 = 0
      linear_combination h011
    · change (E 0 4).coeff 0 = 0
      linear_combination h012
    · change (E 0 4).coeff 1 = 0
      linear_combination h013
    · change (E 0 5).coeff 0 = 0
      linear_combination h014
    · change (E 0 5).coeff 1 = 0
      linear_combination h015
    · change (E 0 6).coeff 0 = 0
      linear_combination h016
    · change (E 0 6).coeff 1 = 0
      linear_combination h017
  have hz1 (j : Fin 7) (d : Fin 1) : (E 1 j).coeff d.val = 0 := by
    fin_cases j <;> fin_cases d
    · change (E 1 0).coeff 0 = 0
      linear_combination h100
    · change (E 1 1).coeff 0 = 0
      linear_combination h102
    · change (E 1 2).coeff 0 = 0
      linear_combination h105
    · change (E 1 3).coeff 0 = 0
      linear_combination - h000 + h001 - h004 + h012 - h014 + h017 + h100 - h101 + h110 - h111 + h114
    · change (E 1 4).coeff 0 = 0
      linear_combination h104
    · change (E 1 5).coeff 0 = 0
      linear_combination - h100 + h101
    · change (E 1 6).coeff 0 = 0
      linear_combination - h100 + h103
  have hzero : E = 0 := by
    funext i j
    apply Polynomial.ext
    intro d
    fin_cases i
    · by_cases hd : d < 2
      · exact (hz0 j ⟨d,hd⟩).trans (coeff_zero _).symm
      · simpa using hcE 0 j d (by simpa using (show 1 < d by omega))
    · by_cases hd : d < 1
      · exact (hz1 j ⟨d,hd⟩).trans (coeff_zero _).symm
      · simpa using hcE 1 j d (by simpa using (show 0 < d by omega))
  refine ⟨hzero,?_⟩
  have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) K[X] => A 0 0) hrel
  simpa [hzero] using h.symm

end FD56
