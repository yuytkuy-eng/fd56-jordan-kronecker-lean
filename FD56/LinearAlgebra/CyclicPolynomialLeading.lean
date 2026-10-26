/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.HessenbergCyclicDeterminant
import FD56.LinearAlgebra.WeightedDeterminantDegree

/-! Highest coefficients of cyclic matrices over a commutative coefficient ring. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

theorem affine_matrix_power_degree_coeff (M : Matrix ι ι R[X])
    (hM : ∀ i j, (M i j).natDegree ≤ 1) (k : ℕ) :
    (∀ i j, ((M^k) i j).natDegree ≤ k) ∧
      (fun i j => ((M^k) i j).coeff k) = (Matrix.of fun i j => (M i j).coeff 1)^k := by
  induction k with
  | zero =>
    constructor
    · intro i j; by_cases hij : i = j <;> simp [Matrix.one_apply,hij]
    · ext i j; by_cases hij : i = j <;> simp [Matrix.one_apply,hij]
  | succ k ih =>
    constructor
    · intro i j
      rw [pow_succ,Matrix.mul_apply]
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro l hl
      exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add (ih.1 i l) (hM l j))
    · ext i j
      rw [pow_succ,Matrix.mul_apply,Polynomial.finset_sum_coeff,pow_succ,Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro l hl
      rw [Polynomial.coeff_mul_add_eq_of_natDegree_le (ih.1 i l) (hM l j)]
      exact congrArg (fun A : Matrix ι ι R => A i l * (M l j).coeff 1) ih.2

theorem firstCyclicMatrix_polynomial_degree_le {n : ℕ}
    (M : Matrix (Fin (n+1)) (Fin (n+1)) R[X])
    (hM : ∀ i j, (M i j).natDegree ≤ 1) :
    (firstCyclicMatrix M).det.natDegree ≤ ∑ i : Fin (n+1), i.val := by
  apply polynomial_det_natDegree_le_row_sum
  intro i j
  exact (affine_matrix_power_degree_coeff M hM i.val).1 0 j

theorem firstCyclicMatrix_polynomial_top_coefficient {n : ℕ}
    (M : Matrix (Fin (n+1)) (Fin (n+1)) R[X])
    (hM : ∀ i j, (M i j).natDegree ≤ 1) :
    (firstCyclicMatrix M).det.coeff (∑ i : Fin (n+1), i.val) =
      (firstCyclicMatrix (Matrix.of fun i j => (M i j).coeff 1)).det := by
  rw [polynomial_det_coefficient_row_sum (firstCyclicMatrix M) (fun i => i.val)
    (fun i j => (affine_matrix_power_degree_coeff M hM i.val).1 0 j)]
  congr 1
  ext i j
  exact congrFun (congrFun (affine_matrix_power_degree_coeff M hM i.val).2 0) j

end FD56
