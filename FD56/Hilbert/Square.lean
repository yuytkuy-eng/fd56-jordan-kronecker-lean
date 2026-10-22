/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SquareLow
import FD56.Hilbert.Adjugate
import FD56.Hilbert.GLRows
import FD56.Hilbert.BlockSum

/-! The actual generic square GL kernel vanishes, and the SL kernel has
one Hilbert index n - 1. These kernel statements do not classify Jordan blocks. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K : Type*} [Field K]

theorem generic_square_slHilbert (n : ℕ) (hn : 0 < n) (d : ℕ) :
    slHilbert (genericAffineSquare K (Fin n) (Fin n))
      (genericAffineRows K (Fin n) (Fin n)) d = d + 1 - (n - 1) := by
  apply le_antisymm (generic_square_slHilbert_upper n hn d)
  exact square_slHilbert_lower n hn _ _ (genericAffineRows_degree K _ _)
    (generic_square_rows_det_ne_zero n) d

theorem generic_square_slHilbert_profile (n : ℕ) (hn : 0 < n) :
    HasHilbertProfile (genericAffineSquare K (Fin n) (Fin n))
      (genericAffineRows K (Fin n) (Fin n)) (fun _ : Fin 1 => n - 1) := by
  intro d
  rw [generic_square_slHilbert n hn d]
  simp [profile]

theorem generic_square_gl_kernel_hilbert (n d : ℕ) :
    Module.finrank (AffineCoefficientField K (MatrixParameters (Fin n) (Fin n)))
      (polynomialKernelAtDegree (glEquationMatrix
        (genericAffineSquare K (Fin n) (Fin n))
        (genericAffineRows K (Fin n) (Fin n))) d) = 0 := by
  rw [gl_kernel_hilbert_of_injective _ _
    (generic_affine_rows_polynomial_injective K (Fin n) (Fin n) (by simp)) d]
  have hdet : (genericAffineRows K (Fin n) (Fin n)).transpose.det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact generic_square_rows_det_ne_zero n
  rw [regular_kernel_hilbert _ hdet d, mul_zero]

end FD56
