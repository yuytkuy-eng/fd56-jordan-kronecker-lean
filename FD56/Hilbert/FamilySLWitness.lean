/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PolynomialMatrix
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-! A sparse polynomial matrix with a low-degree scalar obstruction. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K : Type*} [CommRing K]

/-- A sparse matrix of column degrees at most `(5,5,4)`. -/
def familySLWitness : Matrix (Fin 8) (Fin 3) K[X] :=
  ![![1, 0, 1], ![X ^ 3, X ^ 2, 0], ![X ^ 5, 1, 0],
    ![0, X, 0], ![0, X ^ 4, 0], ![0, X ^ 5, 1],
    ![0, 0, X ^ 2], ![0, 0, X ^ 4]]

theorem familySLWitness_column_degree (i : Fin 8) (j : Fin 3) :
    (familySLWitness (K := K) i j).natDegree ≤ ![5, 5, 4] j := by
  fin_cases i <;> fin_cases j <;> simp [familySLWitness]
  all_goals first
    | exact (natDegree_X_pow_le _).trans (by decide)
    | exact natDegree_X_le.trans (by decide)

theorem familySLWitness_leading_injective :
    Function.Injective (Matrix.mulVec (fun i j =>
      (familySLWitness (K := K) i j).coeff (![5, 5, 4] j))) := by
  intro u v huv
  funext j
  fin_cases j
  · have h := congrFun huv (2 : Fin 8)
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, familySLWitness, coeff_one] using h
  · have h := congrFun huv (5 : Fin 8)
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, familySLWitness, coeff_one] using h
  · have h := congrFun huv (7 : Fin 8)
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, familySLWitness, coeff_one] using h

private theorem familySLWitness_mul_zero (E : Matrix (Fin 3) (Fin 8) K[X])
    (i : Fin 3) :
    (E * familySLWitness (K := K)) i 0 = E i 0 + E i 1 * X ^ 3 + E i 2 * X ^ 5 := by
  simp [familySLWitness, Matrix.mul_apply, Fin.sum_univ_succ]
  ring

private theorem familySLWitness_mul_one (E : Matrix (Fin 3) (Fin 8) K[X])
    (i : Fin 3) :
    (E * familySLWitness (K := K)) i 1 =
      E i 1 * X ^ 2 + E i 2 + E i 3 * X + E i 4 * X ^ 4 + E i 5 * X ^ 5 := by
  simp [familySLWitness, Matrix.mul_apply, Fin.sum_univ_succ]
  ring

private theorem familySLWitness_mul_two (E : Matrix (Fin 3) (Fin 8) K[X])
    (i : Fin 3) :
    (E * familySLWitness (K := K)) i 2 =
      E i 0 + E i 5 + E i 6 * X ^ 2 + E i 7 * X ^ 4 := by
  simp [familySLWitness, Matrix.mul_apply, Fin.sum_univ_succ]
  ring

/-- The first two affine rows already exclude every nonzero scalar product.
The third row and the degree of `c` are unrestricted. -/
theorem familySLWitness_scalar_obstruction
    (E : Matrix (Fin 3) (Fin 8) K[X]) (c : K[X])
    (h0 : ∀ j, (E 0 j).natDegree ≤ 1)
    (h1 : ∀ j, (E 1 j).natDegree ≤ 1)
    (hrel : E * familySLWitness = (-c) • (1 : Matrix (Fin 3) (Fin 3) K[X])) :
    c = 0 := by
  have hc0 (j : Fin 8) (k : ℕ) (hk : 1 < k) : (E 0 j).coeff k = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (h0 j) hk)
  have hc1 (j : Fin 8) (k : ℕ) (hk : 1 < k) : (E 1 j).coeff k = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (h1 j) hk)
  have h00 : E 0 0 + E 0 1 * X ^ 3 + E 0 2 * X ^ 5 = -c := by
    simpa only [familySLWitness_mul_zero, Matrix.smul_apply, Matrix.one_apply,
      if_true, smul_eq_mul, mul_one] using congrArg (fun A => A 0 0) hrel
  have h01 : E 0 1 * X ^ 2 + E 0 2 + E 0 3 * X +
      E 0 4 * X ^ 4 + E 0 5 * X ^ 5 = 0 := by
    simpa [familySLWitness_mul_one, Matrix.smul_apply, Matrix.one_apply]
      using congrArg (fun A => A 0 1) hrel
  have h02 : E 0 0 + E 0 5 + E 0 6 * X ^ 2 + E 0 7 * X ^ 4 = 0 := by
    simpa [familySLWitness_mul_two, Matrix.smul_apply, Matrix.one_apply]
      using congrArg (fun A => A 0 2) hrel
  have h10 : E 1 0 + E 1 1 * X ^ 3 + E 1 2 * X ^ 5 = 0 := by
    simpa [familySLWitness_mul_zero, Matrix.smul_apply, Matrix.one_apply]
      using congrArg (fun A => A 1 0) hrel
  have h11 : E 1 1 * X ^ 2 + E 1 2 + E 1 3 * X +
      E 1 4 * X ^ 4 + E 1 5 * X ^ 5 = -c := by
    simpa [familySLWitness_mul_one, Matrix.smul_apply, Matrix.one_apply]
      using congrArg (fun A => A 1 1) hrel
  have h12 : E 1 0 + E 1 5 + E 1 6 * X ^ 2 + E 1 7 * X ^ 4 = 0 := by
    simpa [familySLWitness_mul_two, Matrix.smul_apply, Matrix.one_apply]
      using congrArg (fun A => A 1 2) hrel
  have ha2 : (E 0 2).coeff 0 = 0 := by
    simpa [coeff_mul_X_pow', coeff_mul_X, coeff_mul_X_zero] using
      congrArg (fun p : K[X] => p.coeff 0) h01
  have hb1 : (E 0 1).coeff 1 = 0 := by
    simpa [coeff_mul_X_pow', coeff_mul_X, hc0] using
      congrArg (fun p : K[X] => p.coeff 3) h01
  have hb5 : (E 0 5).coeff 1 = 0 := by
    simpa [coeff_mul_X_pow', coeff_mul_X, hc0] using
      congrArg (fun p : K[X] => p.coeff 6) h01
  have hb0 : (E 0 0).coeff 1 = 0 := by
    simpa [coeff_mul_X_pow', hb5] using
      congrArg (fun p : K[X] => p.coeff 1) h02
  have hz0 : E 1 0 = 0 := by
    have ha : (E 1 0).coeff 0 = 0 := by
      simpa [coeff_mul_X_pow'] using congrArg (fun p : K[X] => p.coeff 0) h10
    have hb : (E 1 0).coeff 1 = 0 := by
      simpa [coeff_mul_X_pow'] using congrArg (fun p : K[X] => p.coeff 1) h10
    rw [eq_X_add_C_of_natDegree_le_one (h1 0), ha, hb]
    simp
  have hz1 : E 1 1 = 0 := by
    have ha : (E 1 1).coeff 0 = 0 := by
      simpa [coeff_mul_X_pow', hc1] using congrArg (fun p : K[X] => p.coeff 3) h10
    have hb : (E 1 1).coeff 1 = 0 := by
      simpa [coeff_mul_X_pow', hc1] using congrArg (fun p : K[X] => p.coeff 4) h10
    rw [eq_X_add_C_of_natDegree_le_one (h1 1), ha, hb]
    simp
  have hz2 : E 1 2 = 0 := by
    have ha : (E 1 2).coeff 0 = 0 := by
      simpa [coeff_mul_X_pow', hc1] using congrArg (fun p : K[X] => p.coeff 5) h10
    have hb : (E 1 2).coeff 1 = 0 := by
      simpa [coeff_mul_X_pow', hc1] using congrArg (fun p : K[X] => p.coeff 6) h10
    rw [eq_X_add_C_of_natDegree_le_one (h1 2), ha, hb]
    simp
  have hz5 : E 1 5 = 0 := by
    have ha : (E 1 5).coeff 0 = 0 := by
      simpa [coeff_mul_X_pow', hz0] using congrArg (fun p : K[X] => p.coeff 0) h12
    have hb : (E 1 5).coeff 1 = 0 := by
      simpa [coeff_mul_X_pow', hz0] using congrArg (fun p : K[X] => p.coeff 1) h12
    rw [eq_X_add_C_of_natDegree_le_one (h1 5), ha, hb]
    simp
  have hs : E 1 3 * X + E 1 4 * X ^ 4 = -c := by
    simpa [hz1, hz2, hz5] using h11
  apply Polynomial.ext
  intro k
  simp only [coeff_zero]
  by_cases hk : k ≤ 6
  · interval_cases k
    all_goals first
      | have h := congrArg (fun p : K[X] => p.coeff 0) hs
        simpa [coeff_mul_X_pow', coeff_mul_X_zero] using h.symm
      | have h := congrArg (fun p : K[X] => p.coeff 1) h00
        simpa [coeff_mul_X_pow', hb0] using h.symm
      | have h := congrArg (fun p : K[X] => p.coeff 2) h00
        simpa [coeff_mul_X_pow', hc0] using h.symm
      | have h := congrArg (fun p : K[X] => p.coeff 3) hs
        simpa [coeff_mul_X_pow', coeff_mul_X, hc1] using h.symm
      | have h := congrArg (fun p : K[X] => p.coeff 4) h00
        simpa [coeff_mul_X_pow', hc0, hb1] using h.symm
      | have h := congrArg (fun p : K[X] => p.coeff 5) h00
        simpa [coeff_mul_X_pow', hc0, ha2] using h.symm
      | have h := congrArg (fun p : K[X] => p.coeff 6) hs
        simpa [coeff_mul_X_pow', coeff_mul_X, hc1] using h.symm
  · have hk1 : 1 < k := by omega
    have hk3 : 1 < k - 3 := by omega
    have hk5 : 1 < k - 5 := by omega
    have h := congrArg (fun p : K[X] => p.coeff k) h00
    simpa [coeff_mul_X_pow', hc0 _ _ hk1, hc0 _ _ hk3, hc0 _ _ hk5] using h.symm

/-- The degree vector used at the critical truncation of the `(11k,8k)` family. -/
theorem familySLWitness_weighted_scalar_obstruction
    (E : Matrix (Fin 3) (Fin 8) K[X]) (c : K[X])
    (hE : ∀ i j, (E i j).natDegree ≤ ![1, 1, 2] i)
    (hrel : E * familySLWitness = (-c) • (1 : Matrix (Fin 3) (Fin 3) K[X])) :
    c = 0 :=
  familySLWitness_scalar_obstruction E c (hE 0) (hE 1) hrel

end FD56



