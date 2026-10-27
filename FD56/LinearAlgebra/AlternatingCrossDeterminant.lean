/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.HyperbolicSchurDeterminant
import Mathlib.FieldTheory.Separable

/-! The determinant of an alternating cross block is the square of its cross determinant. -/

noncomputable section
namespace FD56
open Matrix Polynomial

theorem alternating_cross_block_det {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (A W : Matrix n n R) : (Matrix.fromBlocks A W (-W.transpose) 0).det = W.det ^ 2 := by
  let J : Matrix (n ⊕ n) (n ⊕ n) R := Matrix.fromBlocks A 1 (-1) 0
  have hJ : J = (hyperbolicCorner A.transpose).transpose := by
    simp [J, hyperbolicCorner, Matrix.fromBlocks_transpose]
  have hdetJ : J.det = 1 := by rw [hJ, Matrix.det_transpose, hyperbolicCorner_det]
  have hfactor : Matrix.fromBlocks A W (-W.transpose) 0 =
      Matrix.fromBlocks 1 0 0 W.transpose * J * Matrix.fromBlocks 1 0 0 W := by
    simp [J, Matrix.fromBlocks_multiply]
  rw [hfactor, Matrix.det_mul, Matrix.det_mul, hdetJ,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, Matrix.det_transpose]
  simp [pow_two]

theorem separable_of_square_eq_scaled_square {K : Type*} [Field K]
    (f g : K[X]) (c : K) (hc : c ≠ 0) (hg : g.Separable)
    (he : f^2 = (C c * g)^2) : f.Separable := by
  have hcg : (C c * g).Separable :=
    Polynomial.Separable.unit_mul (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc)) hg
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with h | h
  · rwa [h]
  · rw [h]
    simpa using Polynomial.Separable.unit_mul (isUnit_one.neg : IsUnit (-1 : K[X])) hcg

end FD56
