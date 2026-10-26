/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.SeparableMatrixDiagonalization
import Mathlib.FieldTheory.SplittingField.Construction

/-! A separable matrix admits distinct diagonal eigenvalues over its splitting field. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

theorem exists_splitting_field_diagonalization (M : Matrix n n K) (hsep : M.charpoly.Separable) :
    ∃ (S T : Matrix n n M.charpoly.SplittingField) (ev : n → M.charpoly.SplittingField),
      Function.Injective ev ∧ S*T = 1 ∧ T*S = 1 ∧
      (M.map (algebraMap K M.charpoly.SplittingField))*S = S*(Matrix.diagonal ev) := by
  apply exists_diagonalization_of_separable_charpoly
  · rw [Matrix.charpoly_map]
    exact hsep.map
  · rw [Matrix.charpoly_map,Polynomial.splits_id_iff_splits]
    exact Polynomial.SplittingField.splits M.charpoly

end FD56
