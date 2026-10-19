/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PredictableDegree

/-! Highest coefficients of polynomial matrix products under degree bounds.
The coefficient may vanish; no exact-degree assumption is made. -/

namespace FD56
open Matrix Polynomial
variable {K l m n : Type*} [Field K]

def matrixCoeff (A : Matrix m n K[X]) (d : ℕ) : Matrix m n K :=
  fun i j => (A i j).coeff d

theorem matrixCoeff_mul [Fintype m] (A : Matrix l m K[X]) (B : Matrix m n K[X])
    (a b : ℕ) (hA : DegreeBound A a) (hB : DegreeBound B b) :
    matrixCoeff (A * B) (a + b) = matrixCoeff A a * matrixCoeff B b := by
  funext i j
  simp only [matrixCoeff, Matrix.mul_apply, Polynomial.finset_sum_coeff]
  apply Finset.sum_congr rfl
  intro k _
  exact Polynomial.coeff_mul_add_eq_of_natDegree_le (hA i k) (hB k j)

theorem degreeBound_pow [Fintype n] [DecidableEq n] (M : Matrix n n K[X])
    (d : ℕ) (hM : DegreeBound M d) (q : ℕ) : DegreeBound (M ^ q) (q * d) := by
  induction q with
  | zero =>
    intro i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  | succ q ih =>
    simpa only [pow_succ, Nat.succ_mul] using degreeBound_mul ih hM

theorem matrixCoeff_pow [Fintype n] [DecidableEq n] (M : Matrix n n K[X])
    (d : ℕ) (hM : DegreeBound M d) (q : ℕ) :
    matrixCoeff (M ^ q) (q * d) = matrixCoeff M d ^ q := by
  induction q with
  | zero =>
    funext i j
    by_cases h : i = j <;> simp [matrixCoeff, Matrix.one_apply, h]
  | succ q ih =>
    rw [pow_succ, Nat.succ_mul,
      matrixCoeff_mul _ _ _ _ (degreeBound_pow M d hM q) hM, ih, pow_succ]

theorem matrixCoeff_mul_column {r : Type*} [Fintype n]
    (A : Matrix m n K[X]) (V : Matrix n r K[X]) (d : ℕ) (a : r → ℕ)
    (hA : DegreeBound A d) (hV : ∀ i j, (V i j).natDegree ≤ a j) :
    ∀ i j, ((A * V) i j).natDegree ≤ d + a j ∧
      ((A * V) i j).coeff (d + a j) =
        (matrixCoeff A d * (show Matrix n r K from fun x k => (V x k).coeff (a k))) i j := by
  intro i j
  constructor
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro k _
    exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hA i k) (hV k j))
  · simp only [Matrix.mul_apply, Polynomial.finset_sum_coeff, matrixCoeff]
    apply Finset.sum_congr rfl
    intro k _
    exact Polynomial.coeff_mul_add_eq_of_natDegree_le (hA i k) (hV k j)

theorem matrix_mul_row_degree [Fintype m] (A : Matrix l m K[X]) (B : Matrix m n K[X])
    (a : l → ℕ) (d : ℕ) (hA : ∀ j x, (A j x).natDegree ≤ a j) (hB : DegreeBound B d) :
    ∀ j y, ((A * B) j y).natDegree ≤ a j + d := by
  intro j y
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro x _
  exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hA j x) (hB x y))

theorem row_coordinates_degree_bound [Fintype m]
    (A : Matrix m n K[X]) (D : Matrix l m K[X]) (e : m → ℕ) (b : l → ℕ)
    (hA : ∀ i j, (A i j).natDegree ≤ e i)
    (hlead : Function.Injective (Matrix.mulVec
      (show Matrix n m K from fun j i => (A i j).coeff (e i))))
    (hbound : ∀ j y, ((D * A) j y).natDegree ≤ b j) :
    ∀ j i, D j i = 0 ∨ (e i ≤ b j ∧ (D j i).natDegree ≤ b j - e i) := by
  intro j
  apply (polynomial_combination_degree_iff A.transpose e (D j) (b j)
    (fun y i => hA i y) hlead).mp
  intro y
  have he : (A.transpose *ᵥ D j) y = (D * A) j y := by
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  rw [he]
  exact hbound j y

end FD56
