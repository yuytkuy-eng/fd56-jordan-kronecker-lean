/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! Common divisors of maximal minors under row operations. -/

namespace FD56
open Matrix
open scoped BigOperators
variable {R n a b : Type*} [CommRing R] [Fintype n] [DecidableEq n] [Fintype a]

theorem maximal_minor_common_divisor_mul_left (A : Matrix a n R) (L : Matrix b a R)
    (d : R) (h : ∀ s : n → a, d ∣ (A.submatrix s id).det) (r : n → b) :
    d ∣ ((L * A).submatrix r id).det := by
  classical
  have he : (L * A).submatrix r id = fun i => ∑ j, L (r i) j • A j := by
    ext i j
    simp [Matrix.mul_apply, Pi.smul_apply, Finset.sum_apply]
  rw [he]
  change d ∣ Matrix.detRowAlternating.toMultilinearMap (fun i => ∑ j, L (r i) j • A j)
  rw [MultilinearMap.map_sum]
  apply Finset.dvd_sum
  intro s _
  change d ∣ Matrix.det (fun i j => L (r i) (s i) * A (s i) j)
  change d ∣ (Matrix.of (fun i j => L (r i) (s i) * (A.submatrix s id) i j)).det
  rw [Matrix.det_mul_column (fun i => L (r i) (s i)) (A.submatrix s id)]
  exact dvd_mul_of_dvd_right (h s) _

theorem maximal_minor_common_divisor_mul_left_iff [DecidableEq a]
    (A : Matrix a n R) (L U : Matrix a a R) (hUL : U * L = 1) (d : R) :
    (∀ r : n → a, d ∣ ((L * A).submatrix r id).det) ↔
      (∀ r : n → a, d ∣ (A.submatrix r id).det) := by
  constructor
  · intro h r
    have hh := maximal_minor_common_divisor_mul_left (L * A) U d h r
    simpa only [← Matrix.mul_assoc, hUL, Matrix.one_mul] using hh
  · intro h r
    exact maximal_minor_common_divisor_mul_left A L d h r

end FD56
