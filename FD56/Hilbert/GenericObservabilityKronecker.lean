/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericObservabilityGL
import FD56.Hilbert.MixedGLKronecker
import FD56.Hilbert.GeneralGLDimension

/-! Arbitrary-depth GL canonical conversion from actual auxiliary profiles.
Polynomial splitting and the two profiles remain explicit hypotheses; the
ambient dimension budget follows from their lengths and degree sums. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem generic_observability_gl_kronecker_of_auxiliary_profiles
    (q : ℕ)
    (R : Matrix n (Fin (q+1) × m) (AffineCoefficientField K (MatrixParameters n m))[X])
    (hR : observabilityMatrix (genericAffineSquare K n m) (genericAffineRows K n m) (q+1) * R = 1)
    (alpha beta : List ℕ)
    (hAlpha : HasMinimalKernelDegrees (observabilityMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m) (q+1)) alpha)
    (hBeta : ∀ (r : ℕ) (Bv : Basis (Fin r) (AffineCoefficientField K (MatrixParameters n m))[X]
      (LinearMap.ker (Matrix.toLin' (observabilityMatrix
        (genericAffineSquare K n m) (genericAffineRows K n m) (q+1))))),
      HasMinimalKernelDegrees ((genericAffineRows K n m) * (genericAffineSquare K n m) ^ (q+1) *
        polynomialKernelBasisMatrix _ Bv).transpose beta)
    (hlen : alpha.length + beta.length = Fintype.card m)
    (hn : Fintype.card n = (q+1)*Fintype.card m + alpha.length)
    (ha : 2*alpha.sum = Fintype.card m*(q+1)*(q+2))
    (hb : beta.sum = alpha.sum + (q+2)*alpha.length) :
    HasKroneckerDecomposition (glKirillovMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m))
      ((degreeConvolution alpha beta).map (fun e => e+q)) := by
  have hlo : (q+1)*Fintype.card m ≤ Fintype.card n := by omega
  have hhi : Fintype.card n ≤ (q+2)*Fintype.card m := by nlinarith
  apply glKirillovMatrix_kronecker _ _ _
    (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m)
    (generic_observability_gl_minimal_degrees q hlo hhi R hR alpha beta hAlpha hBeta)
  rw [observability_gl_dimension_budget _ _ q alpha beta hlen hn ha hb]
  simp only [SLInput,Fintype.card_sum,Fintype.card_prod]
  ring

end FD56
