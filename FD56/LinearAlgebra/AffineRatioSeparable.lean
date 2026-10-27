/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.SquareGLNormalization
import FD56.LinearAlgebra.SplittingMatrixDiagonalization

/-! A square affine pencil with separable determinant has a separable matrix ratio. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

theorem affine_ratio_charpoly (P₀ P₁ V : Matrix n n K) (hVP₁ : V*P₁=1) :
    (-V*P₀).charpoly = C V.det * (affineMatrixPencil P₀ P₁).det := by
  have hmul := affineMatrixPencil_constant_mul V P₀ P₁ (1 : Matrix n n K)
  simp only [Matrix.map_one _ (map_zero C) (map_one C), Matrix.mul_one, hVP₁] at hmul
  have hchar : affineMatrixPencil (V*P₀) 1 = (-V*P₀).charmatrix := by
    funext i j
    by_cases h : i=j
    · subst j
      simp [affineMatrixPencil, Matrix.charmatrix_apply, Matrix.one_apply, add_comm]
    · simp [affineMatrixPencil, Matrix.charmatrix_apply, Matrix.one_apply, h]
  rw [Matrix.charpoly, ← hchar, ← hmul, Matrix.det_mul]
  exact congrArg (fun z => z * (affineMatrixPencil P₀ P₁).det) (Polynomial.C.map_det V).symm

theorem affine_ratio_charpoly_separable (P₀ P₁ V : Matrix n n K) (hVP₁ : V*P₁=1)
    (hp : (affineMatrixPencil P₀ P₁).det.Separable) : (-V*P₀).charpoly.Separable := by
  rw [affine_ratio_charpoly P₀ P₁ V hVP₁]
  apply Polynomial.Separable.unit_mul _ hp
  apply isUnit_C.mpr
  exact isUnit_iff_exists_inv.mpr ⟨P₁.det, by rw [← Matrix.det_mul, hVP₁, Matrix.det_one]⟩

end FD56
