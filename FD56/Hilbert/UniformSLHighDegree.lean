/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.UniformSL

/-! The high-degree uniform SL formula from the exact row-dimension threshold. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem generic_uniform_slHilbert_of_row_dimension (a r : ℕ) (ha : 2 ≤ a) (hr : 0 < r)
    (hm : Fintype.card m = a * r) (hn : Fintype.card n = (a + 1) * r)
    (i₀ : n) (d : ℕ) (hd : a + 1 ≤ d)
    (hdim : a * r + 2 * r ≤ (a * r - r) * (d - (a + 1) + 1)) :
    slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) d =
      Module.finrank (AffineCoefficientField K (MatrixParameters n m))
        (polynomialKernelAtDegree
          (glEquationMatrix (genericAffineSquare K n m) (genericAffineRows K n m)) d) +
        (d + 2) := by
  letI : Nonempty n := ⟨i₀⟩
  have hmn : Fintype.card m < Fintype.card n := by rw [hm, hn]; nlinarith
  have hnm : Fintype.card n < 2 * Fintype.card m := by rw [hm, hn]; nlinarith
  obtain ⟨B, hB, hBL⟩ := generic_uniform_kernel_basis (K := K) a r hr hm hn
  obtain ⟨R, _, hPR⟩ := generic_affine_rows_right_inverse_of_sizes K m n (by omega) hmn
  have hlead := matrix_transpose_injective_of_surjective _
    (generic_affine_rows_leading_surjective K m n hmn.le)
  have hsum : ∑ _ : Fin r, a = Fintype.card m := by simp [hm, Nat.mul_comm]
  have hsize : Fintype.card n = Fintype.card m + Fintype.card (Fin r) := by
    simp only [Fintype.card_fin]
    rw [hm, hn]
    ring
  apply middle_slHilbert_of_scalar_lifts _ _ B R hPR
    (generic_middle_kernel_transfer_injective hnm.le B)
    (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m) i₀ d
  intro c hc
  have hs : ∀ i : Fin r, Function.Surjective (weightedCoefficientMatrix
      (genericAffineRows K n m * genericAffineSquare K n m *
        polynomialKernelBasisMatrix (genericAffineRows K n m) B).transpose
      (fun _ => d - (a + 1)) (fun _ => d - (a + 1) + a + 2)).mulVec := by
    intro i
    apply generic_middle_column_coefficient_surjective B (fun _ => a) hB hsum hsize hmn hnm
    simp only [Fintype.card_fin, hm]
    exact hdim
  obtain ⟨X, U, hX, hU, htr, hPX, hcomm⟩ := middle_sl_scalar_lift _ _ B R hPR
    (fun _ => a) d (fun _ => by dsimp; omega) (genericAffineSquare_degree K n m)
    (genericAffineRows_degree K n m) hB hBL hlead hs c hc
  exact ⟨X, U, hX, hU, (slRadical_iff_equations _ _ _ _).mpr ⟨htr, hPX, c, hcomm⟩, hcomm⟩

theorem generic_uniform_three_slHilbert_high (r : ℕ) (hr : 0 < r)
    (hm : Fintype.card m = 3 * r) (hn : Fintype.card n = 4 * r)
    (i₀ : n) (d : ℕ) (hd : 6 ≤ d) :
    slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) d =
      Module.finrank (AffineCoefficientField K (MatrixParameters n m))
        (polynomialKernelAtDegree
          (glEquationMatrix (genericAffineSquare K n m) (genericAffineRows K n m)) d) +
        (d + 2) := by
  apply generic_uniform_slHilbert_of_row_dimension 3 r (by omega) hr hm hn i₀ d (by omega)
  have hs : 3 * r - r = 2 * r := by omega
  have ht : 3 ≤ d - (3 + 1) + 1 := by omega
  rw [hs]
  nlinarith

theorem generic_uniform_two_slHilbert_high (r : ℕ) (hr : 0 < r)
    (hm : Fintype.card m = 2 * r) (hn : Fintype.card n = 3 * r)
    (i₀ : n) (d : ℕ) (hd : 6 ≤ d) :
    slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) d =
      Module.finrank (AffineCoefficientField K (MatrixParameters n m))
        (polynomialKernelAtDegree
          (glEquationMatrix (genericAffineSquare K n m) (genericAffineRows K n m)) d) +
        (d + 2) := by
  apply generic_uniform_slHilbert_of_row_dimension 2 r (by omega) hr hm hn i₀ d (by omega)
  have hs : 2 * r - r = r := by omega
  have ht : 4 ≤ d - (2 + 1) + 1 := by omega
  rw [hs]
  nlinarith

end FD56
