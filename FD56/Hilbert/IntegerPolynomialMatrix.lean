/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.IntegerPolynomial
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.List.GetD

/-! Integer coefficient convolution certificates for polynomial matrix identities. -/

namespace FD56
open Matrix Polynomial
open scoped BigOperators

def integerPolynomialMatrixProduct {a c : Type*} {n : ℕ}
    (A : Matrix a (Fin n) (List ℤ)) (B : Matrix (Fin n) c (List ℤ)) :
    Matrix a c (List ℤ) := fun i j =>
  (List.ofFn (fun k => integerPolynomialMul (A i k) (B k j))).foldr integerPolynomialAdd []

noncomputable section
variable {K : Type*} [CommRing K]

def integerPolynomialMatrix {a b : Type*} (A : Matrix a b (List ℤ)) : Matrix a b K[X] :=
  fun i j => integerPolynomial (A i j)

theorem integerPolynomial_fold_add (as : List (List ℤ)) :
    integerPolynomial (K := K) (as.foldr integerPolynomialAdd []) =
      (as.map integerPolynomial).sum := by
  induction as with
  | nil => simp
  | cons a as ih => simp only [List.foldr_cons,integerPolynomial_add,List.map_cons,List.sum_cons,ih]

theorem integerPolynomialMatrix_product {a c : Type*} {n : ℕ}
    (A : Matrix a (Fin n) (List ℤ)) (B : Matrix (Fin n) c (List ℤ)) :
    integerPolynomialMatrix (K := K) (integerPolynomialMatrixProduct A B) =
      integerPolynomialMatrix A * integerPolynomialMatrix B := by
  funext i j
  change integerPolynomial ((List.ofFn (fun k => integerPolynomialMul (A i k) (B k j))).foldr
    integerPolynomialAdd []) = ∑ k, integerPolynomial (A i k) * integerPolynomial (B k j)
  rw [integerPolynomial_fold_add,List.map_ofFn,List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro k _
  exact integerPolynomial_mul _ _

theorem integerPolynomialMatrix_mul_of_trim_eq {a c : Type*} {n : ℕ}
    (A : Matrix a (Fin n) (List ℤ)) (B : Matrix (Fin n) c (List ℤ))
    (C : Matrix a c (List ℤ))
    (h : ∀ i j, integerPolynomialTrim (integerPolynomialMatrixProduct A B i j) =
      integerPolynomialTrim (C i j)) :
    integerPolynomialMatrix (K := K) A * integerPolynomialMatrix B = integerPolynomialMatrix C := by
  rw [← integerPolynomialMatrix_product]
  funext i j
  exact integerPolynomial_eq_of_trim_eq (h i j)

theorem integerPolynomial_eq_of_bounded_coeff_eq {as bs : List ℤ} (d : ℕ)
    (ha : as.length ≤ d) (hb : bs.length ≤ d)
    (h : ∀ k : Fin d, as.getD k.val 0 = bs.getD k.val 0) :
    integerPolynomial (K := K) as = integerPolynomial bs := by
  ext k
  rw [integerPolynomial_coeff,integerPolynomial_coeff]
  by_cases hk : k < d
  · exact congrArg (fun z : ℤ => (z : K)) (h ⟨k,hk⟩)
  · rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by omega)]

theorem integerPolynomialMatrix_mul_of_bounded_coeff_eq {a c : Type*} {n : ℕ}
    (A : Matrix a (Fin n) (List ℤ)) (B : Matrix (Fin n) c (List ℤ))
    (C : Matrix a c (List ℤ)) (d : ℕ)
    (hleft : ∀ i j, (integerPolynomialMatrixProduct A B i j).length ≤ d)
    (hright : ∀ i j, (C i j).length ≤ d)
    (h : ∀ i j (k : Fin d), (integerPolynomialMatrixProduct A B i j).getD k.val 0 =
      (C i j).getD k.val 0) :
    integerPolynomialMatrix (K := K) A * integerPolynomialMatrix B = integerPolynomialMatrix C := by
  rw [← integerPolynomialMatrix_product]
  funext i j
  exact integerPolynomial_eq_of_bounded_coeff_eq d (hleft i j) (hright i j) (h i j)

end
end FD56
