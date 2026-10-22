/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericMiddle
import FD56.Hilbert.ColumnSurjectivity

/-! Surjectivity of the generic middle auxiliary coefficient map above
the threshold determined by its balanced kernel degrees. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K n m r : Type*} [Field K] [Fintype n] [Fintype m] [Fintype r]
  [DecidableEq n] [DecidableEq m] [DecidableEq r]

theorem generic_middle_column_coefficient_surjective
    (B : Basis r (Polynomial (AffineCoefficientField K (MatrixParameters n m)))
      (LinearMap.ker (Matrix.toLin' (genericAffineRows K n m))))
    (a : r → ℕ) (hV : ∀ x i,
      (polynomialKernelBasisMatrix (genericAffineRows K n m) B x i).natDegree ≤ a i)
    (ha : ∑ i, a i = Fintype.card m)
    (hr : Fintype.card n = Fintype.card m + Fintype.card r)
    (hmn : Fintype.card m < Fintype.card n)
    (hnm : Fintype.card n < 2 * Fintype.card m)
    (d : ℕ)
    (hd : Fintype.card m + 2 * Fintype.card r ≤
      (Fintype.card m - Fintype.card r) * (d + 1)) :
    Function.Surjective (weightedCoefficientMatrix
      (genericAffineRows K n m * genericAffineSquare K n m *
        polynomialKernelBasisMatrix (genericAffineRows K n m) B).transpose
      (fun _ => d) (fun j => d + a j + 2)).mulVec := by
  let P := genericAffineRows K n m
  let M := genericAffineSquare K n m
  let V := polynomialKernelBasisMatrix P B
  have hsum : ∑ i, (a i + 2) = Fintype.card m + 2 * Fintype.card r := by
    simp [Finset.sum_add_distrib, ha, mul_comm]
  have hh := (hasMinimalKernelDegrees_iff_hilbert _ _).mp
    (generic_middle_auxiliary_minimal_degrees B hmn hnm) d
  rw [balancedDegreeList_hilbert _ _ d (by omega)] at hh
  have hn : Fintype.card n - Fintype.card m = Fintype.card r := by omega
  rw [hn] at hh
  have hs := column_coefficient_surjective_of_kernel_hilbert
    (P * M * V) (fun j => a j + 2) d (by
      intro x j
      change ((P * M * V) x j).natDegree ≤ a j + 2
      have hv := (matrixCoeff_mul_column (P * M) V 2 a
        (degreeBound_mul (genericAffineRows_degree K n m)
          (genericAffineSquare_degree K n m)) hV x j).1
      omega) (by omega) (by simpa only [hsum] using hd) (by simpa only [hsum] using hh)
  simpa only [Nat.add_assoc] using hs

end FD56
