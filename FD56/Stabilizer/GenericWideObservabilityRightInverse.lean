/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.WideObservabilityReindex
import FD56.Stabilizer.GenericAffineDivisorTransfer
import FD56.LinearAlgebra.MaximalMinorLeftInverse

/-! Polynomial right inverses for every strictly wide generic affine observability stack. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem generic_affine_wide_observability_common_divisor_isUnit (q : ℕ)
    (hn : q*Fintype.card m < Fintype.card n)
    (g : (AffineCoefficientField K (MatrixParameters n m))[X])
    (hd : ∀ r : Fin q × m → n,
      g ∣ ((observabilityMatrix (genericAffineSquare K n m) (genericAffineRows K n m) q).submatrix id r).det) :
    IsUnit g := by
  apply affineParameterMap_common_divisor_isUnit
    (fun r : Fin q × m → n =>
      ((observabilityMatrix (universalSquare K n m) (universalRows K n m) q).submatrix id r).det)
    (universal_wide_observability_coprime q hn) g
  intro r
  have he : affineParameterMap K (MatrixParameters n m)
      (((observabilityMatrix (universalSquare K n m) (universalRows K n m) q).submatrix id r).det) =
      ((observabilityMatrix (genericAffineSquare K n m) (genericAffineRows K n m) q).submatrix id r).det := by
    rw [RingHom.map_det]
    change (((observabilityMatrix (universalSquare K n m) (universalRows K n m) q).submatrix id r).map
      (affineParameterMap K (MatrixParameters n m))).det = _
    rw [← Matrix.submatrix_map,observabilityMatrix_map]
    rfl
  rw [he]
  exact hd r

theorem generic_affine_wide_observability_right_inverse (q : ℕ)
    (hn : q*Fintype.card m < Fintype.card n) :
    ∃ R : Matrix n (Fin q × m) (AffineCoefficientField K (MatrixParameters n m))[X],
      observabilityMatrix (genericAffineSquare K n m) (genericAffineRows K n m) q * R = 1 := by
  obtain ⟨L,hL⟩ := left_inverse_of_unit_common_maximal_divisors
    (observabilityMatrix (genericAffineSquare K n m) (genericAffineRows K n m) q).transpose
    (fun g hg => generic_affine_wide_observability_common_divisor_isUnit q hn g (fun r => by
      have hh := hg r
      rwa [← Matrix.transpose_submatrix,Matrix.det_transpose] at hh))
  refine ⟨L.transpose,?_⟩
  have ht := congrArg Matrix.transpose hL
  simpa only [Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.transpose_one] using ht

end FD56
