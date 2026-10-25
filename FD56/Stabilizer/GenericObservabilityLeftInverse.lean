/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GenericObservabilityCoprime
import FD56.LinearAlgebra.MaximalMinorLeftInverse

/-! Polynomial left inverses for strictly tall generic affine observability matrices. -/

namespace FD56
open Matrix Polynomial

variable {K n m : Type*} [Field K] [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m]

theorem generic_affine_observability_left_inverse
    (q : ℕ) (hm : 2 ≤ Fintype.card m) (hn : Fintype.card n < q * Fintype.card m) :
    ∃ L : Matrix n (Fin q × m) (AffineCoefficientField K (MatrixParameters n m))[X],
      L * observabilityMatrix (genericAffineSquare K n m) (genericAffineRows K n m) q = 1 := by
  apply left_inverse_of_unit_common_maximal_divisors
  exact generic_affine_observability_common_divisor_isUnit q hm hn

end FD56
