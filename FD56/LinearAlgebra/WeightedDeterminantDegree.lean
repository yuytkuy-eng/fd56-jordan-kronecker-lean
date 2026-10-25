/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.LinearAlgebra.Matrix.Polynomial

/-! Determinant degrees and highest coefficients with individual row bounds. -/

namespace FD56
open Matrix Polynomial
open scoped BigOperators

/-- The coefficient at the sum of degree bounds is the product of the top coefficients. -/
theorem polynomial_weighted_product_coefficient {R ι : Type*} [CommSemiring R]
    (s : Finset ι) (f : ι → R[X]) (e : ι → ℕ)
    (hf : ∀ i ∈ s, (f i).natDegree ≤ e i) :
    (∏ i ∈ s, f i).coeff (∑ i ∈ s, e i) = ∏ i ∈ s, (f i).coeff (e i) := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty => intro _; simp
  | @insert i s hi ih =>
    intro hf
    have hs : ∀ j ∈ s, (f j).natDegree ≤ e j :=
      fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hp : (∏ j ∈ s, f j).natDegree ≤ ∑ j ∈ s, e j :=
      (Polynomial.natDegree_prod_le s f).trans (Finset.sum_le_sum hs)
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      Polynomial.coeff_mul_add_eq_of_natDegree_le (hf i (Finset.mem_insert_self i s)) hp,
      ih hs, Finset.prod_insert hi]

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

theorem polynomial_det_natDegree_le_row_sum (A : Matrix n n R[X]) (e : n → ℕ)
    (hA : ∀ i j, (A i j).natDegree ≤ e i) :
    A.det.natDegree ≤ ∑ i, e i := by
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ _
  calc
    (Equiv.Perm.sign σ • ∏ i, A (σ i) i).natDegree ≤
        (∏ i, A (σ i) i).natDegree := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
      · rw [h, one_smul]
      · rw [h, Units.neg_smul, one_smul, Polynomial.natDegree_neg]
    _ ≤ ∑ i, (A (σ i) i).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ i, e (σ i) := Finset.sum_le_sum (fun i _ => hA (σ i) i)
    _ = ∑ i, e i := Equiv.sum_comp σ e

theorem polynomial_det_degree_le_row_sum (A : Matrix n n R[X]) (e : n → ℕ)
    (hA : ∀ i j, (A i j).natDegree ≤ e i) :
    A.det.degree ≤ (∑ i, e i : ℕ) :=
  Polynomial.degree_le_of_natDegree_le (polynomial_det_natDegree_le_row_sum A e hA)

/-- The determinant at the weighted top degree is the determinant of the row-leading matrix. -/
theorem polynomial_det_coefficient_row_sum (A : Matrix n n R[X]) (e : n → ℕ)
    (hA : ∀ i j, (A i j).natDegree ≤ e i) :
    A.det.coeff (∑ i, e i) = Matrix.det (fun i j => (A i j).coeff (e i)) := by
  rw [Matrix.det_apply, Polynomial.finset_sum_coeff, Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Polynomial.coeff_smul]
  congr 1
  rw [← Equiv.sum_comp σ e]
  exact polynomial_weighted_product_coefficient Finset.univ (fun i => A (σ i) i)
    (fun i => e (σ i)) (fun i _ => hA (σ i) i)

theorem polynomial_det_ne_zero_of_row_leading_det_ne_zero
    (A : Matrix n n R[X]) (e : n → ℕ)
    (hA : ∀ i j, (A i j).natDegree ≤ e i)
    (hlead : Matrix.det (fun i j => (A i j).coeff (e i)) ≠ 0) : A.det ≠ 0 := by
  intro hz
  apply hlead
  rw [← polynomial_det_coefficient_row_sum A e hA, hz]
  exact Polynomial.coeff_zero _

theorem polynomial_det_natDegree_eq_row_sum
    (A : Matrix n n R[X]) (e : n → ℕ)
    (hA : ∀ i j, (A i j).natDegree ≤ e i)
    (hlead : Matrix.det (fun i j => (A i j).coeff (e i)) ≠ 0) :
    A.det.natDegree = ∑ i, e i := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (polynomial_det_natDegree_le_row_sum A e hA)
  rwa [polynomial_det_coefficient_row_sum A e hA]

theorem polynomial_det_degree_eq_row_sum
    (A : Matrix n n R[X]) (e : n → ℕ)
    (hA : ∀ i j, (A i j).natDegree ≤ e i)
    (hlead : Matrix.det (fun i j => (A i j).coeff (e i)) ≠ 0) :
    A.det.degree = (∑ i, e i : ℕ) := by
  rw [Polynomial.degree_eq_natDegree
    (polynomial_det_ne_zero_of_row_leading_det_ne_zero A e hA hlead),
    polynomial_det_natDegree_eq_row_sum A e hA hlead]

end FD56
