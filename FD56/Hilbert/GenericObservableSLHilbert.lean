/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.ScalarObservability
import FD56.Hilbert.MiddleSLHilbert

/-! Generic scalar commutators are traceless at every observability depth.
The scalar image gives exact GL--SL Hilbert comparison, without a middle-range assumption. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem generic_full_observability_injective (hm : 0<Fintype.card m) :
    Function.Injective (observabilityMatrix (genericAffineSquare K n m)
      (genericAffineRows K n m) (Fintype.card n/Fintype.card m+1)).mulVec := by
  apply generic_terminal_observability_injective
  · exact Nat.div_mul_le_self _ _
  · have hd := Nat.mod_add_div (Fintype.card n) (Fintype.card m)
    have hr := Nat.mod_lt (Fintype.card n) hm
    nlinarith

theorem generic_scalar_commutator_pow_eq_zero (hm : 0<Fintype.card m)
    (X : Matrix n n (AffineCoefficientField K (MatrixParameters n m))[X])
    (U : Matrix n m (AffineCoefficientField K (MatrixParameters n m))[X])
    (c : (AffineCoefficientField K (MatrixParameters n m))[X])
    (hPX : genericAffineRows K n m*X=0)
    (hcomm : genericAffineSquare K n m*X-X*genericAffineSquare K n m=
      U*genericAffineRows K n m+c • 1) :
    X^(Fintype.card n/Fintype.card m+1)=0 :=
  observable_scalar_commutator_pow_eq_zero _ _ X U c hPX hcomm _
    (generic_full_observability_injective hm)

theorem generic_scalar_commutator_trace_zero (hm : 0<Fintype.card m)
    (X : Matrix n n (AffineCoefficientField K (MatrixParameters n m))[X])
    (U : Matrix n m (AffineCoefficientField K (MatrixParameters n m))[X])
    (c : (AffineCoefficientField K (MatrixParameters n m))[X])
    (hPX : genericAffineRows K n m*X=0)
    (hcomm : genericAffineSquare K n m*X-X*genericAffineSquare K n m=
      U*genericAffineRows K n m+c • 1) : Matrix.trace X=0 :=
  observable_scalar_commutator_trace_zero _ _ X U c hPX hcomm _
    (generic_full_observability_injective hm)

theorem generic_slHilbert_eq_gl_add_scalar_range
    (hm : 0<Fintype.card m) (i₀ : n) (d : ℕ) :
    slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) d =
      Module.finrank (AffineCoefficientField K (MatrixParameters n m))
        (polynomialKernelAtDegree
          (glEquationMatrix (genericAffineSquare K n m) (genericAffineRows K n m)) d) +
      Module.finrank (AffineCoefficientField K (MatrixParameters n m))
        (LinearMap.range (boundedSLScalar (genericAffineSquare K n m)
          (genericAffineRows K n m) (genericAffineSquare_degree K n m)
          (genericAffineRows_degree K n m) i₀ d)) := by
  apply slHilbert_eq_gl_add_scalar_range
  intro X U hPX hcomm
  exact generic_scalar_commutator_trace_zero hm X U 0 hPX (by simpa using hcomm)

theorem generic_slHilbert_bounds
    (hm : 0<Fintype.card m) (i₀ : n) (d : ℕ) :
    let g := Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (polynomialKernelAtDegree
        (glEquationMatrix (genericAffineSquare K n m) (genericAffineRows K n m)) d)
    g ≤ slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) d ∧
      slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) d ≤ g+(d+2) := by
  dsimp only
  rw [generic_slHilbert_eq_gl_add_scalar_range hm i₀ d]
  refine ⟨Nat.le_add_right _ _,Nat.add_le_add_left ?_ _⟩
  have hb := Submodule.finrank_le (LinearMap.range (boundedSLScalar
    (genericAffineSquare K n m) (genericAffineRows K n m)
    (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m) i₀ d))
  simpa only [boundedPoly_finrank] using hb

end FD56
