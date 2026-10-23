/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MixedKernelBasis
import FD56.Hilbert.MiddleSLRowObstruction
import FD56.Hilbert.GenericMiddleSLHigh

/-! The generic mixed SL Hilbert function away from its critical degree. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem generic_mixed_slHilbert_low (a u v : ℕ) (ha : 4 ≤ a)
    (hu : 0 < u) (hv : 0 < v)
    (hm : Fintype.card m = a * (u + v) + v)
    (hn : Fintype.card n = Fintype.card m + (u + v))
    (i₀ : n) (d : ℕ) (hd : d ≤ a + 1) :
    slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) d =
      Module.finrank (AffineCoefficientField K (MatrixParameters n m))
        (polynomialKernelAtDegree
          (glEquationMatrix (genericAffineSquare K n m) (genericAffineRows K n m)) d) := by
  have hmn : Fintype.card m < Fintype.card n := by omega
  have hnm : Fintype.card n ≤ 2 * Fintype.card m := by rw [hn, hm]; nlinarith
  obtain ⟨B, hB, hBL⟩ := generic_mixed_kernel_basis (K := K) a u v hu hm hn
  obtain ⟨R, _, hPR⟩ := generic_affine_rows_right_inverse_of_sizes K m n (by omega) hmn
  exact middle_slHilbert_eq_gl_of_column_degree _ _ B R hPR
    (generic_middle_kernel_transfer_injective hnm B) (mixedKernelDegree a u v)
    (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m) hB hBL
    (matrix_transpose_injective_of_surjective _
      (generic_affine_rows_leading_surjective K m n hmn.le)) i₀ d
    (Sum.inr ⟨0, hv⟩) hd

theorem generic_mixed_slHilbert_high (a u v : ℕ) (ha : 4 ≤ a)
    (hu : 0 < u)
    (hm : Fintype.card m = a * (u + v) + v)
    (hn : Fintype.card n = Fintype.card m + (u + v))
    (i₀ : n) (d : ℕ) (hd : a + 3 ≤ d) :
    slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) d =
      Module.finrank (AffineCoefficientField K (MatrixParameters n m))
        (polynomialKernelAtDegree
          (glEquationMatrix (genericAffineSquare K n m) (genericAffineRows K n m)) d) +
        (d + 2) := by
  letI : Nonempty n := ⟨i₀⟩
  have hmn : Fintype.card m < Fintype.card n := by omega
  have hnm : Fintype.card n < 2 * Fintype.card m := by rw [hn, hm]; nlinarith
  obtain ⟨B, hB, hBL⟩ := generic_mixed_kernel_basis (K := K) a u v hu hm hn
  obtain ⟨R, _, hPR⟩ := generic_affine_rows_right_inverse_of_sizes K m n (by omega) hmn
  have hlead := matrix_transpose_injective_of_surjective _
    (generic_affine_rows_leading_surjective K m n hmn.le)
  have hsum : ∑ i, mixedKernelDegree a u v i = Fintype.card m := by
    rw [Fintype.sum_sum_type]
    simp only [mixedKernelDegree_inl, mixedKernelDegree_inr, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    rw [hm]
    ring
  have hsize : Fintype.card n = Fintype.card m + Fintype.card (Fin u ⊕ Fin v) := by
    simpa only [Fintype.card_sum, Fintype.card_fin] using hn
  have hmax (i : Fin u ⊕ Fin v) : mixedKernelDegree a u v i ≤ a + 1 := by
    cases i <;> simp
  have had : ∀ i, mixedKernelDegree a u v i + 1 ≤ d := by
    intro i
    have := hmax i
    omega
  apply middle_slHilbert_of_scalar_lifts _ _ B R hPR
    (generic_middle_kernel_transfer_injective hnm.le B)
    (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m) i₀ d
  intro c hc
  have hs : ∀ i : Fin u ⊕ Fin v, Function.Surjective (weightedCoefficientMatrix
      (genericAffineRows K n m * genericAffineSquare K n m *
        polynomialKernelBasisMatrix (genericAffineRows K n m) B).transpose
      (fun _ => d - (mixedKernelDegree a u v i + 1))
      (fun j => d - (mixedKernelDegree a u v i + 1) + mixedKernelDegree a u v j + 2)).mulVec := by
    intro i
    apply generic_middle_column_coefficient_surjective B (mixedKernelDegree a u v)
      hB hsum hsize hmn hnm
    simp only [Fintype.card_sum, Fintype.card_fin]
    have hrle : u + v ≤ Fintype.card m := by rw [hm]; nlinarith
    have hsub := Nat.sub_add_cancel hrle
    have ht : 2 ≤ d - (mixedKernelDegree a u v i + 1) + 1 := by
      have := hmax i
      omega
    have hsmall : Fintype.card m + 2 * (u + v) ≤ (Fintype.card m - (u + v)) * 2 := by
      have hfour : 4 * (u + v) ≤ Fintype.card m := by rw [hm]; nlinarith
      omega
    exact hsmall.trans (Nat.mul_le_mul_left _ ht)
  obtain ⟨X, U, hX, hU, htr, hPX, hcomm⟩ := middle_sl_scalar_lift _ _ B R hPR
    (mixedKernelDegree a u v) d had (genericAffineSquare_degree K n m)
    (genericAffineRows_degree K n m) hB hBL hlead hs c hc
  exact ⟨X, U, hX, hU, (slRadical_iff_equations _ _ _ _).mpr ⟨htr, hPX, c, hcomm⟩, hcomm⟩

end FD56
