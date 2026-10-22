/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.DualNormalization
import FD56.LinearAlgebra.PolynomialLeading

/-! Constant coordinate changes preserve degree bounds and act on leading
coefficient matrices by the same constant multiplication. -/

namespace FD56
open Matrix Polynomial

variable {K l m n : Type*} [Field K]

theorem constant_mul_column_degree [Fintype m]
    (C : Matrix l m K) (F : Matrix m n K[X]) (e : n → ℕ)
    (hF : ∀ i j, (F i j).natDegree ≤ e j) :
    ∀ i j, ((C.map Polynomial.C * F) i j).natDegree ≤ e j := by
  have hC : DegreeBound (C.map Polynomial.C) 0 := by
    intro i j
    simp
  intro i j
  simpa only [Nat.zero_add] using (matrixCoeff_mul_column _ F 0 e hC hF i j).1

theorem constant_mul_column_leading [Fintype m]
    (C : Matrix l m K) (F : Matrix m n K[X]) (e : n → ℕ) :
    (show Matrix l n K from fun i j => ((C.map Polynomial.C * F) i j).coeff (e j)) =
      C * (show Matrix m n K from fun i j => (F i j).coeff (e j)) := by
  funext i j
  simp only [Matrix.mul_apply, Polynomial.finset_sum_coeff, Matrix.map_apply,
    Polynomial.coeff_C_mul]

theorem mul_constant_row_degree [Fintype m]
    (T : Matrix l m K[X]) (C : Matrix m n K) (f : l → ℕ)
    (hT : ∀ i j, (T i j).natDegree ≤ f i) :
    ∀ i j, ((T * C.map Polynomial.C) i j).natDegree ≤ f i := by
  have hC : DegreeBound (C.map Polynomial.C) 0 := by
    intro i j
    simp
  intro i j
  simpa only [Nat.add_zero] using matrix_mul_row_degree T _ f 0 hT hC i j

theorem mul_constant_row_leading [Fintype m]
    (T : Matrix l m K[X]) (C : Matrix m n K) (f : l → ℕ) :
    (show Matrix l n K from fun i j => ((T * C.map Polynomial.C) i j).coeff (f i)) =
      (show Matrix l m K from fun i j => (T i j).coeff (f i)) * C := by
  funext i j
  simp only [Matrix.mul_apply, Polynomial.finset_sum_coeff, Matrix.map_apply,
    Polynomial.coeff_mul_C]

theorem dual_constant_normalization {r s : Type*} [Fintype r] [Fintype s]
    [DecidableEq r] [DecidableEq s]
    (F : Matrix (r ⊕ s) r K[X]) (T : Matrix s (r ⊕ s) K[X])
    (e : r → ℕ) (f : s → ℕ) (H J : Matrix (r ⊕ s) (r ⊕ s) K)
    (hF : ∀ i j, (F i j).natDegree ≤ e j)
    (hT : ∀ i j, (T i j).natDegree ≤ f i)
    (hJF : J * (show Matrix (r ⊕ s) r K from fun i j => (F i j).coeff (e j)) =
      Matrix.fromRows (1 : Matrix r r K) (0 : Matrix s r K))
    (hTH : (show Matrix s (r ⊕ s) K from fun i j => (T i j).coeff (f i)) * H =
      Matrix.fromCols (0 : Matrix s r K) (1 : Matrix s s K)) :
    (∀ i j, ((J.map Polynomial.C * F) i j).natDegree ≤ e j) ∧
    (∀ i j, ((T * H.map Polynomial.C) i j).natDegree ≤ f i) ∧
    (show Matrix (r ⊕ s) r K from fun i j =>
      ((J.map Polynomial.C * F) i j).coeff (e j)) =
      Matrix.fromRows (1 : Matrix r r K) (0 : Matrix s r K) ∧
    (show Matrix s (r ⊕ s) K from fun i j =>
      ((T * H.map Polynomial.C) i j).coeff (f i)) =
      Matrix.fromCols (0 : Matrix s r K) (1 : Matrix s s K) := by
  exact ⟨constant_mul_column_degree J F e hF, mul_constant_row_degree T H f hT,
    (constant_mul_column_leading J F e).trans hJF,
    (mul_constant_row_leading T H f).trans hTH⟩

end FD56
