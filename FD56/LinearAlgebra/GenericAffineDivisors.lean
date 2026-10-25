/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.AffineShear
import FD56.LinearAlgebra.PolynomialCommonDivisors
import FD56.LinearAlgebra.PolynomialDivisorLocalization
import FD56.LinearAlgebra.MultivariateCommonDivisors
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! Common divisors of polynomial families after invertible substitutions. -/

namespace FD56
open Polynomial

theorem transformed_constants_common_divisor_isUnit
    {R K ι : Type*} [CommRing R] [IsDomain R] [NormalizedGCDMonoid R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (e : R[X] ≃+* R[X]) (f : ι → R)
    (h : ∀ d, (∀ i, d ∣ f i) → IsUnit d) :
    ∀ d : K[X], (∀ i, d ∣ (e (C (f i))).map (algebraMap R K)) → IsUnit d :=
  polynomial_common_divisor_isUnit_fraction_map (fun i => e (C (f i)))
    (common_divisor_isUnit_under_equiv e (fun i => C (f i))
      (polynomial_constants_common_divisor_isUnit f h))

noncomputable section
variable {R σ : Type*} [CommRing R]

def polynomialVariableSwap :
    (MvPolynomial σ R)[X] ≃+* MvPolynomial σ R[X] :=
  ((MvPolynomial.optionEquivLeft R σ).symm.trans
    (MvPolynomial.optionEquivRight R σ)).toRingEquiv

theorem polynomialVariableSwap_C_X (i : σ) :
    polynomialVariableSwap (C (MvPolynomial.X i : MvPolynomial σ R)) =
      MvPolynomial.X i := by
  change MvPolynomial.optionEquivRight R σ
    ((MvPolynomial.optionEquivLeft R σ).symm (C (MvPolynomial.X i))) = _
  rw [← MvPolynomial.optionEquivLeft_X_some, AlgEquiv.symm_apply_apply]
  exact MvPolynomial.optionEquivRight_X_some R σ i

theorem polynomialVariableSwap_X :
    polynomialVariableSwap (X : (MvPolynomial σ R)[X]) = MvPolynomial.C X := by
  change MvPolynomial.optionEquivRight R σ
    ((MvPolynomial.optionEquivLeft R σ).symm X) = _
  rw [← MvPolynomial.optionEquivLeft_X_none, AlgEquiv.symm_apply_apply]
  exact MvPolynomial.optionEquivRight_X_none R σ

def polynomialAffineShear :
    (MvPolynomial (σ ⊕ σ) R)[X] ≃+* (MvPolynomial (σ ⊕ σ) R)[X] :=
  polynomialVariableSwap.trans
    ((affineShear (X : R[X])).toRingEquiv.trans polynomialVariableSwap.symm)

theorem polynomialAffineShear_inl (i : σ) :
    polynomialAffineShear (C (MvPolynomial.X (Sum.inl i) : MvPolynomial (σ ⊕ σ) R)) =
      C (MvPolynomial.X (Sum.inl i)) + X * C (MvPolynomial.X (Sum.inr i)) := by
  change polynomialVariableSwap.symm
    (affineShear X (polynomialVariableSwap (C (MvPolynomial.X (Sum.inl i))))) = _
  rw [polynomialVariableSwap_C_X, affineShear_inl]
  apply polynomialVariableSwap.injective
  simp only [RingEquiv.apply_symm_apply, map_add, map_mul,
    polynomialVariableSwap_C_X, polynomialVariableSwap_X]

theorem polynomialAffineShear_inr (i : σ) :
    polynomialAffineShear (C (MvPolynomial.X (Sum.inr i) : MvPolynomial (σ ⊕ σ) R)) =
      C (MvPolynomial.X (Sum.inr i)) := by
  change polynomialVariableSwap.symm
    (affineShear X (polynomialVariableSwap (C (MvPolynomial.X (Sum.inr i))))) = _
  rw [polynomialVariableSwap_C_X, affineShear_inr]
  apply polynomialVariableSwap.injective
  simp only [RingEquiv.apply_symm_apply, polynomialVariableSwap_C_X]

theorem polynomialAffineShear_X :
    polynomialAffineShear (X : (MvPolynomial (σ ⊕ σ) R)[X]) = X := by
  change polynomialVariableSwap.symm
    (affineShear X (polynomialVariableSwap X)) = _
  rw [polynomialVariableSwap_X]
  have hc : affineShear (X : R[X]) (MvPolynomial.C X : MvPolynomial (σ ⊕ σ) R[X]) =
      MvPolynomial.C X := by simp [affineShear, affineShearHom]
  rw [hc]
  apply polynomialVariableSwap.injective
  simp only [RingEquiv.apply_symm_apply, polynomialVariableSwap_X]

end
/-- A generic affine line preserves the absence of a common polynomial factor. -/
theorem generic_affine_line_common_divisor_isUnit
    {K F σ ι : Type*} [Field K] [Field F] [Fintype σ]
    [Algebra (MvPolynomial (σ ⊕ σ) K) F]
    [IsFractionRing (MvPolynomial (σ ⊕ σ) K) F]
    (f : ι → MvPolynomial σ K)
    (h : ∀ d, (∀ i, d ∣ f i) → IsUnit d) :
    ∀ d : F[X], (∀ i, d ∣
      (polynomialAffineShear (C (MvPolynomial.rename Sum.inl (f i)))).map
        (algebraMap (MvPolynomial (σ ⊕ σ) K) F)) → IsUnit d := by
  letI : NormalizedGCDMonoid (MvPolynomial (σ ⊕ σ) K) := Classical.choice inferInstance
  exact transformed_constants_common_divisor_isUnit polynomialAffineShear
    (fun i => MvPolynomial.rename Sum.inl (f i)) (rename_inl_common_divisor_isUnit f h)

end FD56
