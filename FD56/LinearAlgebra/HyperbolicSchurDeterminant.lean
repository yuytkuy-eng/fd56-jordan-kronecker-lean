/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-! Eliminating a hyperbolic pair with one-sided coupling does not change the determinant. -/

noncomputable section
namespace FD56
open Matrix

variable {R a b : Type*} [CommRing R] [Fintype a] [Fintype b]
  [DecidableEq a] [DecidableEq b]

def hyperbolicCorner (A : Matrix a a R) : Matrix (a ⊕ a) (a ⊕ a) R :=
  Matrix.fromBlocks A (-1) 1 0

def hyperbolicCornerInverse (A : Matrix a a R) : Matrix (a ⊕ a) (a ⊕ a) R :=
  Matrix.fromBlocks 0 1 (-1) A

theorem hyperbolicCorner_inverse (A : Matrix a a R) :
    hyperbolicCorner A*hyperbolicCornerInverse A=1 ∧
      hyperbolicCornerInverse A*hyperbolicCorner A=1 := by
  constructor <;> simp [hyperbolicCorner,hyperbolicCornerInverse,
    Matrix.fromBlocks_multiply,Matrix.fromBlocks_one]

theorem hyperbolicCorner_det (A : Matrix a a R) : (hyperbolicCorner A).det=1 := by
  let L : Matrix (a ⊕ a) (a ⊕ a) R := Matrix.fromBlocks 1 1 0 1
  have hL : L.det=1 := by simp [L,Matrix.det_fromBlocks_zero₂₁]
  have hprod : hyperbolicCorner A*L=Matrix.fromBlocks A (A-1) 1 1 := by
    simp [hyperbolicCorner,L,Matrix.fromBlocks_multiply,sub_eq_add_neg]
  have hh := congrArg Matrix.det hprod
  rw [Matrix.det_mul,hL,mul_one,Matrix.det_fromBlocks_one₂₂,
    Matrix.mul_one,sub_sub_cancel,Matrix.det_one] at hh
  exact hh

theorem hyperbolic_schur_det (A : Matrix a a R) (B : Matrix a b R)
    (C : Matrix b a R) (D : Matrix b b R) :
    (Matrix.fromBlocks (hyperbolicCorner A) (Matrix.fromRows B 0)
      (Matrix.fromCols C 0) D).det=D.det := by
  letI : Invertible (hyperbolicCorner A) :=
    ⟨hyperbolicCornerInverse A,(hyperbolicCorner_inverse A).2,(hyperbolicCorner_inverse A).1⟩
  rw [Matrix.det_fromBlocks₁₁,hyperbolicCorner_det,one_mul]
  change (D-Matrix.fromCols C 0*hyperbolicCornerInverse A*Matrix.fromRows B 0).det=D.det
  simp only [hyperbolicCornerInverse,Matrix.fromCols_mul_fromBlocks,Matrix.fromCols_mul_fromRows,
    Matrix.mul_zero,Matrix.zero_mul,Matrix.mul_one,zero_add,add_zero,sub_zero]

end FD56
