/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.CorankOneObservabilityHilbert
import FD56.Hilbert.MinimalProfile

/-! The actual corank-one auxiliary degree at every depth with a split prefix. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem generic_corank_one_all_depths_beta_degrees {r : Type*} [Fintype r] (q : ℕ)
    (hm : 2 ≤ Fintype.card m)
    (hn : Fintype.card n+1=(q+1)*Fintype.card m)
    (B : Basis r
      (AffineCoefficientField K (MatrixParameters n m))[X]
      (LinearMap.ker (Matrix.toLin' (observabilityMatrix
        (genericAffineSquare K n m) (genericAffineRows K n m) q))))
    (R : Matrix n (Fin q × m) (AffineCoefficientField K (MatrixParameters n m))[X])
    (hR : observabilityMatrix (genericAffineSquare K n m) (genericAffineRows K n m) q * R = 1) :
    HasMinimalKernelDegrees
      (genericAffineRows K n m * (genericAffineSquare K n m)^q *
        polynomialKernelBasisMatrix (observabilityMatrix
          (genericAffineSquare K n m) (genericAffineRows K n m) q) B).transpose
      [Fintype.card m*(∑ i : Fin (q+1), (i.val+1))-(q+1)] := by
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  have hlo : q*Fintype.card m ≤ Fintype.card n := by nlinarith
  rw [← observability_beta_kernel_finrank q
    (genericAffineSquare K n m) (genericAffineRows K n m) B R hR
    (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m)
    (generic_observability_row_leading_injective q hlo) d,
    generic_corank_one_all_depths_bounded_beta_hilbert q d hm hn]
  simp

end FD56
