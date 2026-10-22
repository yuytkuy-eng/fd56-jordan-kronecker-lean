/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SingletonBasis
import FD56.Hilbert.OneColumnSL
import FD56.Stabilizer.GenericMiddleRank

/-! Generic SL minimal degrees when the number of columns exceeds the number
of rows by one. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem generic_one_more_column_sl_minimal_degrees (i₀ : n)
    (hm : 0 < Fintype.card m) (hnm : Fintype.card n = Fintype.card m + 1) :
    HasMinimalKernelDegrees
      (slEquationMatrix (genericAffineSquare K n m) (genericAffineRows K n m) i₀)
      (List.replicate (Fintype.card m) (Fintype.card m + 1)) := by
  obtain ⟨B, hB, hBL⟩ := generic_one_more_column_kernel_basis (K := K) hnm
  obtain ⟨R, _, hPR⟩ := generic_affine_rows_right_inverse_of_sizes K m n hm (by omega)
  have hlead := matrix_transpose_injective_of_surjective _
    (generic_affine_rows_leading_surjective K m n (by omega))
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [one_column_sl_kernel_hilbert _ _ B R hPR
    (generic_middle_kernel_transfer_injective (by omega) B) (Fintype.card m)
    (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m) hB hBL hlead i₀ d]
  simp

theorem generic_one_more_column_slHilbert (i₀ : n)
    (hm : 0 < Fintype.card m) (hnm : Fintype.card n = Fintype.card m + 1) (d : ℕ) :
    slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) d =
      Fintype.card m * (d - Fintype.card m) := by
  rw [slHilbert_eq_matrix_kernel _ _ i₀]
  have hh := (hasMinimalKernelDegrees_iff_hilbert _ _).mp
    (generic_one_more_column_sl_minimal_degrees (K := K) i₀ hm hnm) d
  simpa using hh

end FD56
