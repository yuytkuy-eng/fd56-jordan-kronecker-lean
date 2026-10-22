/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GenericRectangular
import FD56.Hilbert.GLRows
import FD56.Hilbert.SLRows
import FD56.Stabilizer.GenericSLWitness
import FD56.Stabilizer.RectangularSL

/-! Actual generic GL and SL Hilbert functions throughout the range m > n. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem generic_above_gl_kernel_hilbert
    (hnm : Fintype.card n < Fintype.card m) (d : ℕ) :
    Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (polynomialKernelAtDegree (glEquationMatrix
        (genericAffineSquare K n m) (genericAffineRows K n m)) d) =
          Fintype.card n * ((Fintype.card m - Fintype.card n) * (d + 1) - Fintype.card n) := by
  rw [gl_kernel_hilbert_of_injective _ _
    (generic_affine_rows_polynomial_injective K n m (le_of_lt hnm)) d,
    generic_transpose_kernel_hilbert hnm d]

theorem generic_above_gl_kernel_profile
    (hnm : Fintype.card n < Fintype.card m) (d : ℕ) :
    Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (polynomialKernelAtDegree (glEquationMatrix
        (genericAffineSquare K n m) (genericAffineRows K n m)) d) =
      ∑ ij : n × (Fin (Fintype.card n % (Fintype.card m - Fintype.card n)) ⊕
          Fin ((Fintype.card m - Fintype.card n) -
            Fintype.card n % (Fintype.card m - Fintype.card n))),
        (d + 1 - rectangularBlockLengths (Fintype.card n)
          (Fintype.card m - Fintype.card n) ij.2) := by
  rw [generic_above_gl_kernel_hilbert hnm d]
  simp only [Fintype.sum_prod_type, rectangularBlockLengths, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]
  rw [rectangular_balanced_hilbert_sizes _ _ d (by omega)]

theorem generic_above_slHilbert_low (i₀ : n)
    (hnm : Fintype.card n < Fintype.card m) (d : ℕ)
    (hd : (Fintype.card m - Fintype.card n) * (d + 1) < Fintype.card n) :
    slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) d = 0 := by
  let N := Fintype.card n
  let s := Fintype.card m - Fintype.card n
  have hs : 0 < s := by dsimp [s]; omega
  let e := rectangularBlockLengths N s
  have he : (∀ i, d < e i) ∧ (∃ i, d + 1 < e i) := by
    apply rectangular_balanced_low_degree
    rw [rectangular_balanced_block_count N s hs, ← rectangular_balanced_rows N s hs]
    exact hd
  let Q : Matrix n m K[X] := balancedRectangularWitness hnm
  apply generic_slHilbert_zero_of_witness Q.transpose
    (fun i j => balancedRectangularWitness_degree hnm j i)
    (rectangularBlockPencil_submatrix_transpose_injective e
      (balancedRowEquiv hnm) (balancedColumnEquiv hnm)) i₀ d
  intro U c hU hdeg
  exact (rectangular_scalar_low_degree_zero_reindex e
    (balancedRowEquiv hnm) (balancedColumnEquiv hnm) d he.1 he.2 U c hU hdeg).1

theorem generic_above_slHilbert (i₀ : n)
    (hnm : Fintype.card n < Fintype.card m) (d : ℕ) :
    slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) d =
      (Fintype.card n * (Fintype.card m - Fintype.card n) + 1) * (d + 1) -
        (Fintype.card n * Fintype.card n - 1) := by
  let N := Fintype.card n
  let s := Fintype.card m - Fintype.card n
  have hn : 0 < N := Fintype.card_pos_iff.mpr ⟨i₀⟩
  have hs : 0 < s := by dsimp [s]; omega
  by_cases hd : N ≤ s * (d + 1)
  · rw [slHilbert_of_transpose_coefficient_surjective _ _
      (genericAffineRows_degree K n m) i₀ d
      (generic_transpose_coefficient_surjective hnm d hd)]
    have hm : Fintype.card m = N + s := by dsimp [N, s]; omega
    change N * Fintype.card m * (d + 1) - N * N * (d + 2) + (d + 2) =
      (N * s + 1) * (d + 1) - (N * N - 1)
    conv_lhs => rw [hm, mul_assoc, mul_assoc, ← Nat.mul_sub_left_distrib,
      rectangular_coefficient_difference]
    exact rectangular_sl_hilbert_above N s d hn hd
  · have hd' : s * (d + 1) < N := by omega
    rw [generic_above_slHilbert_low i₀ hnm d hd']
    exact (rectangular_sl_hilbert_below N s d hs hd').symm

theorem generic_above_slHilbert_profile (i₀ : n)
    (hnm : Fintype.card n < Fintype.card m) :
    HasHilbertProfile (genericAffineSquare K n m) (genericAffineRows K n m)
      (rectangularBlockLengths (Fintype.card n * Fintype.card n - 1)
        (Fintype.card n * (Fintype.card m - Fintype.card n) + 1)) := by
  intro d
  rw [generic_above_slHilbert i₀ hnm d]
  symm
  simpa [profile, rectangularBlockLengths, Fintype.sum_sum_type] using
    rectangular_balanced_hilbert_sizes (Fintype.card n * Fintype.card n - 1)
      (Fintype.card n * (Fintype.card m - Fintype.card n) + 1) d (by omega)

end FD56
