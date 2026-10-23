/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MixedTwoSingleScalarWitness
import Mathlib.Tactic.LinearCombination

/-! Fixed scalar obstructions for the two-high-column cubic induction. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K : Type*} [Field K] [CharZero K]

def mixedOneTwoEvenBase : Matrix (Fin 4) (Fin 2) K[X] :=
  ![![X^4,0], ![X^2+X^3,X^4], ![-1,X^2], ![0,-1]]

def mixedOneTwoOddBase : Matrix (Fin 5) (Fin 3) K[X] :=
  ![![X^3,0,0], ![X+X^2,X^4,0], ![-1,X^2,X^4], ![0,-1,X^2], ![0,0,-1]]

omit [CharZero K] in
private theorem scalar_relation_coeff {m n : Type*} [Fintype n] [DecidableEq m]
    (G : Matrix n m K[X]) (E : Matrix m n K[X]) (c : K[X])
    (hrel : E*G=(-c) • (1 : Matrix m m K[X])) (i j : m) (k : ℕ) :
    ((E*G) i j).coeff k + (if i=j then c.coeff k else 0) = 0 := by
  have h := congrArg (fun Z : Matrix m m K[X] => (Z i j).coeff k) hrel
  by_cases hij : i=j
  · simp [Matrix.smul_apply,Matrix.one_apply,hij] at h ⊢
    exact add_eq_zero_iff_eq_neg.mpr h
  · simpa [Matrix.smul_apply,Matrix.one_apply,hij] using h

omit [CharZero K] in
theorem mixedOneTwoEvenBase_scalar_obstruction
    (E : Matrix (Fin 2) (Fin 4) K[X]) (c : K[X])
    (hE : DegreeBound E 2) (hc : c.natDegree ≤ 6)
    (hrel : E*mixedOneTwoEvenBase (K := K)=(-c) • (1 : Matrix (Fin 2) (Fin 2) K[X]))
    (h0 : c.coeff 0=0) (h5 : c.coeff 5=0) (h6 : c.coeff 6=0) : c=0 := by
  have hz (i : Fin 2) (j : Fin 4) (k : ℕ) (hk : 2<k) : (E i j).coeff k=0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hE i j) hk)
  have h (i j : Fin 2) (k : ℕ) := scalar_relation_coeff mixedOneTwoEvenBase E c hrel i j k
  have h001 := h 0 0 1
  have h013 := h 0 1 3
  have h002 := h 0 0 2
  have h003 := h 0 0 3
  have h014 := h 0 1 4
  have h015 := h 0 1 5
  have h101 := h 1 0 1
  have h113 := h 1 1 3
  have h102 := h 1 0 2
  have h103 := h 1 0 3
  have h114 := h 1 1 4
  have h115 := h 1 1 5
  norm_num [mixedOneTwoEvenBase,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,
    coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz] at h001 h013 h002 h003 h014 h015 h101 h113 h102 h103 h114 h115
  have h1 : c.coeff 1=0 := by linear_combination h001+h013
  have h23 : c.coeff 2-2*c.coeff 3=0 := by linear_combination h002-2*h003+h014+2*h015
  have h3 : c.coeff 3=0 := by linear_combination h113-h101
  have h45 : c.coeff 4+2*c.coeff 5=0 := by linear_combination h102-2*h103+h114+2*h115
  have h2 : c.coeff 2=0 := by linear_combination h23+2*h3
  have h4 : c.coeff 4=0 := by linear_combination h45-2*h5
  apply Polynomial.ext
  intro k
  by_cases hk : k≤6
  · interval_cases k <;> simp [h0,h1,h2,h3,h4,h5,h6]
  · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hc (by omega)),coeff_zero]

omit [CharZero K] in
theorem mixedOneTwoEvenBase_scalar_zero
    (E : Matrix (Fin 2) (Fin 4) K[X]) (c : K[X])
    (hE : DegreeBound E 1) (hc : c.natDegree ≤ 5)
    (hrel : E*mixedOneTwoEvenBase (K := K)=(-c) • (1 : Matrix (Fin 2) (Fin 2) K[X])) : c=0 := by
  have hz (i : Fin 2) (j : Fin 4) (k : ℕ) (hk : 1<k) : (E i j).coeff k=0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hE i j) hk)
  have h (i j : Fin 2) (k : ℕ) := scalar_relation_coeff mixedOneTwoEvenBase E c hrel i j k
  have h000 := h 0 0 0
  have h012 := h 0 1 2
  have h102 := h 1 0 2
  have h103 := h 1 0 3
  have h115 := h 1 1 5
  norm_num [mixedOneTwoEvenBase,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,
    coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz] at h000 h012 h102 h103 h115
  have h0 : c.coeff 0=0 := by linear_combination h000+h012
  have h5 : c.coeff 5=0 := by linear_combination h102-h103+h115
  apply mixedOneTwoEvenBase_scalar_obstruction E c (fun i j => (hE i j).trans (by decide))
    (hc.trans (by decide)) hrel h0 h5
  exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hc (by decide))

theorem mixedOneTwoOddBase_scalar_obstruction
    (E : Matrix (Fin 3) (Fin 5) K[X]) (c : K[X])
    (hE : ∀ i j, (E i j).natDegree ≤ if i=0 then 4 else 3) (hc : c.natDegree ≤ 7)
    (hrel : E*mixedOneTwoOddBase (K := K)=(-c) • (1 : Matrix (Fin 3) (Fin 3) K[X]))
    (h0 : c.coeff 0=0) : c=0 := by
  have hz0 (j : Fin 5) (k : ℕ) (hk : 4<k) : (E 0 j).coeff k=0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (by simpa using hE 0 j) hk)
  have hz1 (j : Fin 5) (k : ℕ) (hk : 3<k) : (E 1 j).coeff k=0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (by simpa using hE 1 j) hk)
  have hz2 (j : Fin 5) (k : ℕ) (hk : 3<k) : (E 2 j).coeff k=0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (by simpa using hE 2 j) hk)
  have h (i j : Fin 3) (k : ℕ) := scalar_relation_coeff mixedOneTwoOddBase E c hrel i j k
  have h001 := h 0 0 1
  have h002 := h 0 0 2
  have h013 := h 0 1 3
  have h014 := h 0 1 4
  have h015 := h 0 1 5
  have h025 := h 0 2 5
  have h026 := h 0 2 6
  have h027 := h 0 2 7
  have h100 := h 1 0 0
  have h101 := h 1 0 1
  have h102 := h 1 0 2
  have h112 := h 1 1 2
  have h113 := h 1 1 3
  have h114 := h 1 1 4
  have h115 := h 1 1 5
  have h124 := h 1 2 4
  have h125 := h 1 2 5
  have h126 := h 1 2 6
  have h127 := h 1 2 7
  have h200 := h 2 0 0
  have h201 := h 2 0 1
  have h202 := h 2 0 2
  have h212 := h 2 1 2
  have h213 := h 2 1 3
  have h214 := h 2 1 4
  have h215 := h 2 1 5
  have h224 := h 2 2 4
  have h225 := h 2 2 5
  have h226 := h 2 2 6
  have h227 := h 2 2 7
  norm_num [mixedOneTwoOddBase,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,
    Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Fin.ext_iff,
    coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz0,hz1,hz2] at h001 h002 h013 h014 h015 h025 h026 h027 h100 h101 h102 h112 h113 h114 h115 h124 h125 h126 h127 h200 h201 h202 h212 h213 h214 h215 h224 h225 h226 h227
  have h12 : -6*c.coeff 1+4*c.coeff 2=0 := by
    linear_combination -6*h001+4*h002-3*h013+2*h014-4*h015-3*h025+2*h026+4*h027
  have h2 : c.coeff 2=0 := by linear_combination -2*h100+h112+h124
  have h34 : c.coeff 3-2*c.coeff 4=0 := by
    linear_combination 2*h101+h113-2*h114+h125+2*h126
  have h345 : -c.coeff 3+c.coeff 4-c.coeff 5=0 := by
    linear_combination -2*h101+h102-h113+h114-h115-h125+h127
  have h4 : c.coeff 4=0 := by linear_combination -2*h200+h212+h224
  have h56 : c.coeff 5+2*c.coeff 6=0 := by
    linear_combination 2*h201+h213-2*h214+h225+2*h226
  have h57 : -c.coeff 5+c.coeff 7=0 := by
    linear_combination -2*h201+h202-h213+h214-h215-h225+h227
  have h1 : c.coeff 1=0 := by linear_combination (-1/6 : K)*h12+(2/3 : K)*h2
  have h3 : c.coeff 3=0 := by linear_combination h34+2*h4
  have h5 : c.coeff 5=0 := by linear_combination -h345-h3+h4
  have h6 : c.coeff 6=0 := by linear_combination (1/2 : K)*h56-(1/2 : K)*h5
  have h7 : c.coeff 7=0 := by linear_combination h57+h5
  apply Polynomial.ext
  intro k
  by_cases hk : k≤7
  · interval_cases k <;> simp [h0,h1,h2,h3,h4,h5,h6,h7]
  · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hc (by omega)),coeff_zero]

theorem mixedOneTwoOddBase_scalar_zero
    (E : Matrix (Fin 3) (Fin 5) K[X]) (c : K[X])
    (hE : ∀ i j, (E i j).natDegree ≤ if i=0 then 3 else 2) (hc : c.natDegree ≤ 6)
    (hrel : E*mixedOneTwoOddBase (K := K)=(-c) • (1 : Matrix (Fin 3) (Fin 3) K[X])) : c=0 := by
  have hz (j : Fin 5) (k : ℕ) (hk : 3<k) : (E 0 j).coeff k=0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (by simpa using hE 0 j) hk)
  have h (i j : Fin 3) (k : ℕ) := scalar_relation_coeff mixedOneTwoOddBase E c hrel i j k
  have h000 := h 0 0 0
  have h012 := h 0 1 2
  have h024 := h 0 2 4
  norm_num [mixedOneTwoOddBase,Matrix.mul_apply,Fin.sum_univ_succ,mul_add,
    Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Fin.ext_iff,
    coeff_add,coeff_sub,coeff_neg,coeff_mul_X_pow',coeff_mul_X,hz] at h000 h012 h024
  have h0 : c.coeff 0=0 := by linear_combination h000+(1/2 : K)*h012+(1/2 : K)*h024
  apply mixedOneTwoOddBase_scalar_obstruction E c _ (hc.trans (by decide)) hrel h0
  intro i j
  exact (hE i j).trans (by split_ifs <;> omega)

end FD56
