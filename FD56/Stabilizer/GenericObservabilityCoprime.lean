/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.ObservabilityCoprime
import FD56.Stabilizer.GenericAffineDivisorTransfer

/-! Maximal observability minors of a strictly tall generic affine pencil are coprime. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K n m : Type*} [Field K] [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m]

theorem generic_affine_observability_common_divisor_isUnit
    (q : ℕ) (hm : 2 ≤ Fintype.card m) (hn : Fintype.card n < q * Fintype.card m)
    (g : (AffineCoefficientField K (MatrixParameters n m))[X])
    (hdiv : ∀ r : n → Fin q × m,
      g ∣ ((observabilityMatrix (genericAffineSquare K n m) (genericAffineRows K n m) q).submatrix
        r id).det) : IsUnit g := by
  apply affineParameterMap_common_divisor_isUnit
    (fun r : n → Fin q × m =>
      ((observabilityMatrix (universalSquare K n m) (universalRows K n m) q).submatrix
        r id).det)
    (universal_observability_common_divisor_isUnit q hm hn) g
  intro r
  rw [observabilityMatrix_minor_map]
  exact hdiv r

theorem generic_affine_observability_minor_gcd_eq_one
    [NormalizedGCDMonoid (AffineCoefficientField K (MatrixParameters n m))[X]]
    (q : ℕ) (hm : 2 ≤ Fintype.card m) (hn : Fintype.card n < q * Fintype.card m) :
    observabilityMinorGCD (genericAffineSquare K n m) (genericAffineRows K n m) q = 1 := by
  have h := generic_affine_observability_common_divisor_isUnit (K := K) q hm hn
    (observabilityMinorGCD (genericAffineSquare K n m) (genericAffineRows K n m) q)
    (fun r => Finset.gcd_dvd (Finset.mem_univ r))
  simpa only [observabilityMinorGCD, Finset.normalize_gcd] using normalize_eq_one.mpr h

end FD56
