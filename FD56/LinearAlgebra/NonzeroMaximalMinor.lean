/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.MaximalMinorDivisors
import FD56.LinearAlgebra.PolynomialBezout

/-! Independent matrix columns have a nonsingular coordinate minor. -/

namespace FD56
open Matrix
variable {K a n : Type*} [Field K] [Fintype a] [Fintype n] [DecidableEq a] [DecidableEq n]

theorem exists_nonzero_maximal_minor_of_injective (A : Matrix a n K)
    (hA : Function.Injective A.mulVec) :
    ∃ r : n → a, (A.submatrix r id).det ≠ 0 := by
  obtain ⟨E, hE⟩ := matrix_left_inverse_of_injective A hA
  by_contra hn
  have hz : ∀ r : n → a, (A.submatrix r id).det = 0 := by simpa using hn
  have hh := maximal_minor_common_divisor_mul_left A E 0
    (fun r => by simp [hz r]) id
  rw [hE] at hh
  simp at hh

theorem exists_nonsingular_coordinate_embedding (A : Matrix a n K)
    (hA : Function.Injective A.mulVec) :
    ∃ r : n ↪ a, (A.submatrix r id).det ≠ 0 := by
  obtain ⟨r, hr⟩ := exists_nonzero_maximal_minor_of_injective A hA
  have hi : Function.Injective r := by
    intro i j hij
    by_contra hn
    apply hr
    apply Matrix.det_zero_of_row_eq hn
    funext k
    simp [Matrix.submatrix, hij]
  exact ⟨⟨r, hi⟩, hr⟩

end FD56
