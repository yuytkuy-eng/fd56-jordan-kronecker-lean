/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! Maximal-minor divisibility under column operations. -/

namespace FD56
open Matrix
open scoped BigOperators

variable {R m n l : Type*} [CommRing R]
  [Fintype m] [Fintype n] [Fintype l] [DecidableEq m]

/-- Expanding columns before collecting repeated selections gives a rectangular product formula. -/
theorem det_rectangular_product_sum
    (A : Matrix m n R) (B : Matrix n m R) :
    (A * B).det = ∑ r : m → n,
      (A.submatrix id r).det * ∏ i, B (r i) i := by
  classical
  calc
    (A * B).det = ∑ r : m → n, ∑ s : Equiv.Perm m,
        (s.sign : R) * ∏ i, A (s i) (r i) * B (r i) i := by
      simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum,
        Finset.mul_sum, Fintype.piFinset_univ]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Matrix.det_apply', Finset.sum_mul]
      simp only [Matrix.submatrix_apply,id_eq,Finset.prod_mul_distrib,mul_assoc]

theorem dvd_det_rectangular_product_of_maximal_minors
    (A : Matrix m n R) (B : Matrix n m R) (d : R)
    (hd : ∀ r : m → n, d ∣ (A.submatrix id r).det) : d ∣ (A * B).det := by
  classical
  rw [det_rectangular_product_sum]
  exact Finset.dvd_sum (fun r _ => dvd_mul_of_dvd_left (hd r) _)

omit [Fintype l] in
theorem maximal_column_minors_dvd_mul_right
    (A : Matrix m n R) (S : Matrix n l R) (d : R)
    (hd : ∀ r : m → n, d ∣ (A.submatrix id r).det) :
    ∀ r : m → l, d ∣ ((A * S).submatrix id r).det := by
  intro r
  have he : (A * S).submatrix id r = A * S.submatrix id r := rfl
  rw [he]
  exact dvd_det_rectangular_product_of_maximal_minors A _ d hd

theorem maximal_column_minors_dvd_iff_of_right_inverse [DecidableEq n]
    (A : Matrix m n R) (S U : Matrix n n R) (hSU : S * U = 1) (d : R) :
    (∀ r : m → n, d ∣ (A.submatrix id r).det) ↔
      (∀ r : m → n, d ∣ ((A * S).submatrix id r).det) := by
  constructor
  · exact maximal_column_minors_dvd_mul_right A S d
  · intro hd
    have hh := maximal_column_minors_dvd_mul_right (A * S) U d hd
    simpa only [Matrix.mul_assoc,hSU,Matrix.mul_one] using hh

theorem dvd_power_of_rectangular_product_eq_scalar
    (A : Matrix m n R) (B : Matrix n m R) (c d : R)
    (hAB : A * B = c • (1 : Matrix m m R))
    (hd : ∀ r : m → n, d ∣ (A.submatrix id r).det) :
    d ∣ c ^ Fintype.card m := by
  have hh := dvd_det_rectangular_product_of_maximal_minors A B d hd
  simpa only [hAB,Matrix.det_smul,Matrix.det_one,mul_one] using hh

end FD56
