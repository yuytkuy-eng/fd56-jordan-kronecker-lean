/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.CubicRowExtension

/-! Fixed coefficient conditions for the two parity classes of cubic extensions. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K : Type*} [Field K] [CharZero K]

def mixedOneTwoEvenAdjugate : Matrix (Fin 2) (Fin 2) K[X] :=
  ![![2-X, X^2], ![-1, 2+X]]

def mixedOneTwoOddAdjugate : Matrix (Fin 2) (Fin 2) K[X] :=
  ![![2*X^2, -4+6*X], ![2+3*X, 9]]

theorem mixedOneTwoEven_jet_zero
    (Q P : Matrix (Fin 2) (Fin 2) K[X]) (c : K[X])
    (hQ : DegreeBound Q 1)
    (h : (4 : K[X]) • Q = (X^3 : K[X]) • P+c • mixedOneTwoEvenAdjugate) :
    ∀ k < 3, c.coeff k=0 := by
  have hz (i j : Fin 2) : (Q i j).coeff 2=0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hQ i j) (by omega))
  have h01 := congrArg (fun A : Matrix (Fin 2) (Fin 2) K[X] => (A 0 1).coeff 2) h
  have h10 := congrArg (fun A : Matrix (Fin 2) (Fin 2) K[X] => (A 1 0).coeff 2) h
  have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) K[X] => (A 0 0).coeff 2) h
  norm_num [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
    mixedOneTwoEvenAdjugate, coeff_add, coeff_sub, mul_sub, mul_add,
    coeff_X_pow_mul', coeff_mul_X_pow', coeff_mul_X, hz] at h01 h10 h00
  intro k hk
  interval_cases k
  · exact h01.symm
  · linear_combination h00+2*h10
  · exact h10

theorem mixedOneTwoOdd_jet_zero
    (Q P : Matrix (Fin 2) (Fin 2) K[X]) (c : K[X])
    (hQ : ∀ i, (Q i 1).natDegree ≤ 0)
    (h : (8 : K[X]) • Q = (X^3 : K[X]) • P+c • mixedOneTwoOddAdjugate) :
    ∀ k < 3, c.coeff k=0 := by
  have hz (i : Fin 2) (k : ℕ) (hk : 0<k) : (Q i 1).coeff k=0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hQ i) hk)
  have h11 := congrArg (fun A : Matrix (Fin 2) (Fin 2) K[X] => (A 1 1).coeff 1) h
  have h01 := congrArg (fun A : Matrix (Fin 2) (Fin 2) K[X] => (A 0 1).coeff 1) h
  have h12 := congrArg (fun A : Matrix (Fin 2) (Fin 2) K[X] => (A 1 1).coeff 2) h
  norm_num [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
    mixedOneTwoOddAdjugate, coeff_add, coeff_sub, mul_sub, mul_add,
    coeff_X_pow_mul', coeff_mul_X_pow', coeff_mul_X, ← mul_assoc, hz] at h11 h01 h12
  intro k hk
  interval_cases k
  · linear_combination -h01/6+2*h11/3
  · exact h11
  · exact h12

theorem mixedOneTwoOdd_jet_zero_of_constant
    (Q P : Matrix (Fin 2) (Fin 2) K[X]) (c : K[X])
    (hQ : ∀ i, (Q i 1).natDegree ≤ 1) (hc : c.coeff 0=0)
    (h : (8 : K[X]) • Q = (X^3 : K[X]) • P+c • mixedOneTwoOddAdjugate) :
    ∀ k < 3, c.coeff k=0 := by
  have hz (i : Fin 2) : (Q i 1).coeff 2=0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hQ i) (by omega))
  have h02 := congrArg (fun A : Matrix (Fin 2) (Fin 2) K[X] => (A 0 1).coeff 2) h
  have h12 := congrArg (fun A : Matrix (Fin 2) (Fin 2) K[X] => (A 1 1).coeff 2) h
  norm_num [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
    mixedOneTwoOddAdjugate, coeff_add, coeff_sub, mul_sub, mul_add,
    coeff_X_pow_mul', coeff_mul_X_pow', coeff_mul_X, ← mul_assoc, hz] at h02 h12
  intro k hk
  interval_cases k
  · exact hc
  · linear_combination -h02/6+2*h12/3
  · exact h12

end FD56
