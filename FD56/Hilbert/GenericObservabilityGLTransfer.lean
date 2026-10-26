/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericObservabilityGL
import FD56.Stabilizer.GenericWideObservabilityRightInverse

/-! The generic GL degree transfer needs only the two actual auxiliary profiles. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem generic_observability_gl_minimal_degrees_of_auxiliary_profiles
    (q : ℕ) (hsize : (q+1)*Fintype.card m < Fintype.card n)
    (hsize' : Fintype.card n ≤ (q+2)*Fintype.card m)
    (alpha beta : List ℕ)
    (hAlpha : HasMinimalKernelDegrees (observabilityMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m) (q+1)) alpha)
    (hBeta : ∀ (r : ℕ) (Bv : Basis (Fin r) (AffineCoefficientField K (MatrixParameters n m))[X]
      (LinearMap.ker (Matrix.toLin' (observabilityMatrix
        (genericAffineSquare K n m) (genericAffineRows K n m) (q+1))))),
      HasMinimalKernelDegrees ((genericAffineRows K n m) * (genericAffineSquare K n m) ^ (q+1) *
        polynomialKernelBasisMatrix _ Bv).transpose beta) :
    HasMinimalKernelDegrees (glEquationMatrix (genericAffineSquare K n m) (genericAffineRows K n m))
      ((degreeConvolution alpha beta).map (fun e => e+q)) := by
  obtain ⟨R,hR⟩ := generic_affine_wide_observability_right_inverse (K := K) (q+1) hsize
  exact generic_observability_gl_minimal_degrees q hsize.le hsize' R hR alpha beta hAlpha hBeta

end FD56
