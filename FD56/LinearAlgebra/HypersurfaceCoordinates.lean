/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PolynomialHypersurface
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.Polynomial.Basic

/-! The remaining variables stay independent after one positive-degree relation. -/

namespace FD56
open Polynomial

theorem hypersurface_remaining_coordinates_independent {K σ : Type*} [Field K]
    (g : (MvPolynomial σ K)[X]) (hg : 0 < g.natDegree) :
    AlgebraicIndependent K (fun i : σ =>
      Ideal.Quotient.mk (Ideal.span ({g} : Set (MvPolynomial σ K)[X]))
        (C (MvPolynomial.X i))) := by
  let φ : MvPolynomial σ K →ₐ[K]
      (MvPolynomial σ K)[X] ⧸ Ideal.span ({g} : Set (MvPolynomial σ K)[X]) :=
    (Ideal.Quotient.mkₐ K (Ideal.span ({g} : Set (MvPolynomial σ K)[X]))).comp
      (Polynomial.CAlgHom (R := K) (A := MvPolynomial σ K))
  have hφ : Function.Injective φ := polynomial_quotient_coefficients_injective g hg
  exact (MvPolynomial.algebraicIndependent_X σ K).map' (f := φ) hφ

end FD56
