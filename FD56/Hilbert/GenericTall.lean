/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.Tall
import FD56.Stabilizer.GenericRows

/-! Generic GL and full SL Hilbert functions in the range m ≥ 2n. -/

noncomputable section
namespace FD56
open Matrix Polynomial

theorem tall_hilbert_arithmetic (n m d : ℕ) (h : 2 * n ≤ m) :
    n * m * (d + 1) - n * n * (d + 2) = n * (m - 2 * n) * (d + 1) + n * n * d := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  have he : n * (2 * n + c) * (d + 1) =
      n * n * (d + 2) + (n * c * (d + 1) + n * n * d) := by ring
  rw [he, Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]

theorem tall_sl_hilbert_arithmetic (n m d : ℕ) (hn : 0 < n) (h : 2 * n ≤ m) :
    (n * m * (d + 1) - n * n * (d + 2)) + (d + 2) =
      (n * (m - 2 * n) + 2) * (d + 1) + (n * n - 1) * d := by
  rw [tall_hilbert_arithmetic n m d h]
  have hn₂ : 1 ≤ n * n := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have he : n * n = (n * n - 1) + 1 := (Nat.sub_add_cancel hn₂).symm
  conv_lhs => rw [he]
  ring

variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem generic_tall_gl_kernel_hilbert
    (hnm : 2 * Fintype.card n ≤ Fintype.card m) (d : ℕ) :
    Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (polynomialKernelAtDegree (glEquationMatrix
        (genericAffineSquare K n m) (genericAffineRows K n m)) d) =
      Fintype.card n * (Fintype.card m - 2 * Fintype.card n) * (d + 1) +
        Fintype.card n * Fintype.card n * d := by
  rw [tall_gl_kernel_hilbert _ _ (genericAffineRows_degree K n m)
    (generic_affine_coefficient_columns_injective K n m hnm)]
  exact tall_hilbert_arithmetic _ _ d hnm

theorem generic_tall_slHilbert (i₀ : n)
    (hnm : 2 * Fintype.card n ≤ Fintype.card m) (d : ℕ) :
    slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) d =
      (Fintype.card n * (Fintype.card m - 2 * Fintype.card n) + 2) * (d + 1) +
        (Fintype.card n * Fintype.card n - 1) * d := by
  rw [tall_slHilbert _ _ (genericAffineRows_degree K n m) i₀
    (generic_affine_coefficient_columns_injective K n m hnm)]
  have hn : 0 < Fintype.card n := Fintype.card_pos_iff.mpr ⟨i₀⟩
  exact tall_sl_hilbert_arithmetic _ _ d hn hnm

theorem generic_tall_slHilbert_profile (i₀ : n)
    (hnm : 2 * Fintype.card n ≤ Fintype.card m) :
    HasHilbertProfile (genericAffineSquare K n m) (genericAffineRows K n m)
      (Sum.elim (fun _ : Fin (Fintype.card n * (Fintype.card m - 2 * Fintype.card n) + 2) => 0)
        (fun _ : Fin (Fintype.card n * Fintype.card n - 1) => 1)) := by
  intro d
  rw [generic_tall_slHilbert i₀ hnm d]
  simp [profile, Fintype.sum_sum_type]

end FD56
