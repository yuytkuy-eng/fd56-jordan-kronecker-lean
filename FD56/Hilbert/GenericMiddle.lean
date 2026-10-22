/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GenericBeta
import FD56.Hilbert.MiddleSizedWitness
import FD56.Hilbert.GenericMinimal
import FD56.Hilbert.ConvolutionDegrees
import FD56.Stabilizer.GenericMiddleRank

/-! Generic auxiliary and GL kernel minimal degrees in the range m < n < 2m. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem generic_middle_beta_hilbert
    (hmn : Fintype.card m < Fintype.card n)
    (hnm : Fintype.card n < 2 * Fintype.card m) (d : ℕ) :
    Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (boundedBetaKernel (genericAffineSquare K n m) (genericAffineRows K n m) d) =
      Fintype.card m * (2 * d + 3) - Fintype.card n * (d + 3) := by
  obtain ⟨M, P, hM, hP, hH⟩ := exists_middle_sized_beta_witness (K := K) hmn hnm
  exact generic_beta_hilbert_of_witness M P hM hP d (hH d)

theorem generic_middle_auxiliary_minimal_degrees
    {r : Type*} [Fintype r] [DecidableEq r]
    (Bv : Basis r (Polynomial (AffineCoefficientField K (MatrixParameters n m)))
      (LinearMap.ker (Matrix.toLin' (genericAffineRows K n m))))
    (hmn : Fintype.card m < Fintype.card n)
    (hnm : Fintype.card n < 2 * Fintype.card m) :
    HasMinimalKernelDegrees
      (genericAffineRows K n m * genericAffineSquare K n m *
        polynomialKernelBasisMatrix (genericAffineRows K n m) Bv).transpose
      (balancedDegreeList (Fintype.card m + 2 * (Fintype.card n - Fintype.card m))
        (Fintype.card m - (Fintype.card n - Fintype.card m))) := by
  obtain ⟨R, _, hPR⟩ := generic_affine_rows_right_inverse_of_sizes K m n (by omega) hmn
  have hlead := matrix_transpose_injective_of_surjective _
    (generic_affine_rows_leading_surjective K m n hmn.le)
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [← beta_kernel_finrank _ _ Bv R hPR (genericAffineSquare_degree K n m)
    (genericAffineRows_degree K n m) hlead d, generic_middle_beta_hilbert hmn hnm d,
    balancedDegreeList_hilbert _ _ d (by omega)]
  have hn : Fintype.card n = Fintype.card m + (Fintype.card n - Fintype.card m) := by omega
  conv_lhs => rw [hn]
  exact middle_beta_dimension_identity _ _ d (by omega)

theorem generic_middle_gl_minimal_degrees
    (hmn : Fintype.card m < Fintype.card n)
    (hnm : Fintype.card n < 2 * Fintype.card m) :
    HasMinimalKernelDegrees
      (glEquationMatrix (genericAffineSquare K n m) (genericAffineRows K n m))
      (degreeConvolution
        (balancedDegreeList (Fintype.card m) (Fintype.card n - Fintype.card m))
        (balancedDegreeList (Fintype.card m + 2 * (Fintype.card n - Fintype.card m))
          (Fintype.card m - (Fintype.card n - Fintype.card m)))) := by
  obtain ⟨r, Bv, a, hV, hVL, ha⟩ := generic_rows_minimal_degrees (K := K) hmn
  obtain ⟨s, Bt, b, hT, hTL, hb⟩ := generic_middle_auxiliary_minimal_degrees Bv hmn hnm
  obtain ⟨R, _, hPR⟩ := generic_affine_rows_right_inverse_of_sizes K m n (by omega) hmn
  have hlead := matrix_transpose_injective_of_surjective _
    (generic_affine_rows_leading_surjective K m n hmn.le)
  exact middle_gl_minimal_degrees_of_bases _ _ Bv Bt R hPR
    (generic_middle_kernel_transfer_injective hnm.le Bv) a b
    (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m)
    hV hT hVL hTL hlead _ _ ha hb

end FD56
