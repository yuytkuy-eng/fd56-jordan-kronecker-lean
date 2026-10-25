/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.ObservabilityCovariance
import FD56.LinearAlgebra.MaximalMinorKernel

/-! A common divisor that vanishes in a field forces an observability kernel. -/

namespace FD56
open Matrix
variable {R F n m : Type*} [CommRing R] [Field F]
  [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

theorem normalized_observability_kernel_of_common_divisor (φ : R →+* F)
    (M : Matrix n n R) (P : Matrix m n R) (q : ℕ) (g : R)
    (hg : ∀ r : n → Fin q × m, g ∣ ((observabilityMatrix M P q).submatrix r id).det)
    (hzero : φ g = 0) :
    ∃ (i : n) (v : n → F), observabilityMatrix (M.map φ) (P.map φ) q *ᵥ v = 0 ∧ v i = 1 := by
  apply normalized_kernel_of_zero_maximal_minors
  intro r
  rw [← observabilityMatrix_minor_map φ M P q r]
  obtain ⟨s, hs⟩ := hg r
  rw [hs, map_mul, hzero, zero_mul]

end FD56
