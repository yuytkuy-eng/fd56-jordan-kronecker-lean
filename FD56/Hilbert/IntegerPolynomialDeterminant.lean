/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.IntegerPolynomialMatrix
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! Recursive integer coefficient certificates for polynomial determinants. -/

namespace FD56
open Matrix Polynomial
open scoped BigOperators

def integerPolynomialDeterminant : {n : ℕ} → Matrix (Fin n) (Fin n) (List ℤ) → List ℤ
  | 0, _ => [1]
  | n + 1, A =>
    (List.ofFn (fun j : Fin (n + 1) =>
      (integerPolynomialMul (A 0 j)
        (integerPolynomialDeterminant (A.submatrix Fin.succ j.succAbove))).map
          (((-1 : ℤ) ^ j.val) * ·))).foldr integerPolynomialAdd []

noncomputable section
variable {K : Type*} [CommRing K]

theorem integerPolynomial_determinant {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (List ℤ)) :
    integerPolynomial (K := K) (integerPolynomialDeterminant A) =
      (integerPolynomialMatrix A).det := by
  induction n with
  | zero => simp [integerPolynomialDeterminant, Matrix.det_isEmpty]
  | succ n ih =>
    rw [integerPolynomialDeterminant, integerPolynomial_fold_add, List.map_ofFn,
      List.sum_ofFn, Matrix.det_succ_row_zero]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [Function.comp_apply]
    rw [integerPolynomial_map_mul, integerPolynomial_mul, ih]
    simp only [Int.cast_pow, Int.cast_neg, Int.cast_one, mul_assoc]
    rfl

theorem integerPolynomial_determinant_of_trim_eq {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (List ℤ)) (cs : List ℤ)
    (h : integerPolynomialTrim (integerPolynomialDeterminant A) =
      integerPolynomialTrim cs) :
    (integerPolynomialMatrix (K := K) A).det = integerPolynomial cs := by
  rw [← integerPolynomial_determinant]
  exact integerPolynomial_eq_of_trim_eq h

end
end FD56
