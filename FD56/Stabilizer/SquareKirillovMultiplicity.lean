/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.SquareKirillovDeterminant
import Mathlib.Algebra.Polynomial.RingDivision

/-! Exact determinant root multiplicities in the square GL family.
Determinant multiplicities alone do not determine regular block sizes. -/

noncomputable section
namespace FD56
open Polynomial Matrix
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

private theorem rootMultiplicity_of_associated {p q : K[X]} (h : Associated p q)
    (hp : p ≠ 0) (a : K) : rootMultiplicity a p = rootMultiplicity a q := by
  have hq : q ≠ 0 := h.ne_zero_iff.mp hp
  apply Nat.le_antisymm
  · apply (le_rootMultiplicity_iff hq).mpr
    exact h.dvd_iff_dvd_right.mp (pow_rootMultiplicity_dvd p a)
  · apply (le_rootMultiplicity_iff hp).mpr
    exact h.dvd_iff_dvd_right.mpr (pow_rootMultiplicity_dvd q a)

private theorem rootMultiplicity_power (p : K[X]) (hp : p ≠ 0) (a : K) (k : ℕ) :
    rootMultiplicity a (p ^ k) = k * rootMultiplicity a p := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero k hp) hp), ih]
    exact (Nat.succ_mul k _).symm

theorem glKirillovMatrix_square_det_rootMultiplicity
    (M P : Matrix n n K[X]) (hP : P.det ≠ 0) (a : K) :
    rootMultiplicity a (glKirillovMatrix M P).det =
      2 * Fintype.card n * rootMultiplicity a P.det := by
  have h := glKirillovMatrix_square_det_associated M P
  have hh : (glKirillovMatrix M P).det ≠ 0 :=
    h.ne_zero_iff.mpr (pow_ne_zero _ hP)
  exact (rootMultiplicity_of_associated h hh a).trans
    (rootMultiplicity_power P.det hP a (2 * Fintype.card n))

end FD56
