/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.CorankOnePolynomialDegree
import FD56.Hilbert.GenericObservabilityLeading
import FD56.Stabilizer.GenericWideObservabilityRightInverse

/-! The first auxiliary minimal degree for every corank-one observability depth. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem generic_corank_one_observability_alpha_degrees (q : ℕ)
    (hn : Fintype.card n = q*Fintype.card m+1) :
    HasMinimalKernelDegrees (observabilityMatrix (genericAffineSquare K n m)
      (genericAffineRows K n m) q)
      [Fintype.card m * ∑ i : Fin q, (i.val+1)] := by
  have hh := corank_one_polynomial_minimal_degree
    (observabilityMatrix (genericAffineSquare K n m) (genericAffineRows K n m) q)
    (by simpa only [Fintype.card_prod,Fintype.card_fin] using hn)
    (fun ij : Fin q × m => ij.1.val+1)
    (fun ij j => (observability_polynomial_degree_top _ _ q
      (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m) ij j).1)
    (generic_observability_row_leading_injective q (by omega))
    (generic_affine_wide_observability_common_divisor_isUnit q (by omega))
  convert hh using 2
  simp only [Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,smul_eq_mul,
    Finset.mul_sum]

end FD56
