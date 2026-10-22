/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericMiddleSurjectivity
import FD56.Hilbert.BalancedDegrees
import FD56.Hilbert.MiddleSLScalarLifts
import FD56.Hilbert.MiddleSLHilbert

/-! Above an explicit threshold the generic middle SL scalar image is
the whole bounded polynomial space. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem generic_middle_slHilbert_bounds
    (i₀ : n) (hmn : Fintype.card m < Fintype.card n)
    (hnm : Fintype.card n < 2 * Fintype.card m) (d : ℕ) :
    let g := Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (polynomialKernelAtDegree
        (glEquationMatrix (genericAffineSquare K n m) (genericAffineRows K n m)) d)
    g ≤ slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) d ∧
      slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) d ≤ g + (d + 2) := by
  obtain ⟨_, B, _, _, _, _⟩ := generic_rows_minimal_degrees (K := K) hmn
  obtain ⟨R, _, hPR⟩ := generic_affine_rows_right_inverse_of_sizes K m n (by omega) hmn
  have he := middle_slHilbert_eq_gl_add_scalar_range _ _ B R hPR
    (generic_middle_kernel_transfer_injective hnm.le B)
    (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m) i₀ d
  dsimp only
  rw [he]
  refine ⟨Nat.le_add_right _ _, Nat.add_le_add_left ?_ _⟩
  have hb := Submodule.finrank_le (LinearMap.range (boundedSLScalar
    (genericAffineSquare K n m) (genericAffineRows K n m)
    (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m) i₀ d))
  simpa only [boundedPoly_finrank] using hb

theorem generic_middle_slHilbert_high
    (i₀ : n) (hmn : Fintype.card m < Fintype.card n)
    (hnm : Fintype.card n < 2 * Fintype.card m) (d : ℕ)
    (hd : Fintype.card m / (Fintype.card n - Fintype.card m) +
      (Fintype.card m + 2 * (Fintype.card n - Fintype.card m)) /
        (Fintype.card m - (Fintype.card n - Fintype.card m)) + 2 ≤ d) :
    slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) d =
      Module.finrank (AffineCoefficientField K (MatrixParameters n m))
        (polynomialKernelAtDegree
          (glEquationMatrix (genericAffineSquare K n m) (genericAffineRows K n m)) d) +
        (d + 2) := by
  letI : Nonempty n := ⟨i₀⟩
  obtain ⟨r, B, a, hV, hVL, haperm⟩ := generic_rows_minimal_degrees (K := K) hmn
  obtain ⟨hr, ha, hmax⟩ := balancedDegreeList_ofFn_properties a
    (Fintype.card m) (Fintype.card n - Fintype.card m) (by omega) haperm
  obtain ⟨R, _, hPR⟩ := generic_affine_rows_right_inverse_of_sizes K m n (by omega) hmn
  have hlead := matrix_transpose_injective_of_surjective _
    (generic_affine_rows_leading_surjective K m n hmn.le)
  apply middle_slHilbert_of_scalar_lifts _ _ B R hPR
    (generic_middle_kernel_transfer_injective hnm.le B)
    (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m) i₀ d
  intro c hc
  have hd' : Fintype.card m / (Fintype.card n - Fintype.card m) + 2 ≤ d :=
    (Nat.add_le_add_right (Nat.le_add_right _ _) 2).trans hd
  have had : ∀ i, a i + 1 ≤ d := by
    intro i
    have := hmax i
    omega
  have hs : ∀ i, Function.Surjective (weightedCoefficientMatrix
      (genericAffineRows K n m * genericAffineSquare K n m *
        polynomialKernelBasisMatrix (genericAffineRows K n m) B).transpose
      (fun _ => d - (a i + 1)) (fun j => d - (a i + 1) + a j + 2)).mulVec := by
    intro i
    apply generic_middle_column_coefficient_surjective B a hV ha
      (by simpa only [Fintype.card_fin] using (show Fintype.card n = Fintype.card m + r by omega))
      hmn hnm
    simp only [Fintype.card_fin, hr]
    let s := Fintype.card m - (Fintype.card n - Fintype.card m)
    let b := Fintype.card m + 2 * (Fintype.card n - Fintype.card m)
    have hsp : 0 < s := by dsimp [s]; omega
    have hmod := Nat.mod_lt b hsp
    have hdiv := Nat.mod_add_div b s
    have hbound : b ≤ s * (b / s + 1) := by nlinarith
    have hi : b / s + 1 ≤ d - (a i + 1) + 1 := by
      have := hmax i
      dsimp only [b, s]
      omega
    exact hbound.trans (Nat.mul_le_mul_left s hi)
  obtain ⟨X, U, hX, hU, htr, hPX, hcomm⟩ := middle_sl_scalar_lift
    _ _ B R hPR a d had (genericAffineSquare_degree K n m)
    (genericAffineRows_degree K n m) hV hVL hlead hs c hc
  exact ⟨X, U, hX, hU, (slRadical_iff_equations _ _ _ _).mpr ⟨htr, hPX, c, hcomm⟩, hcomm⟩

end FD56
