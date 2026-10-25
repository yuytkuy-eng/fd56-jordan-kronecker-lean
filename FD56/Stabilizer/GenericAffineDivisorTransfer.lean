/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GenericPencil
import FD56.LinearAlgebra.GenericAffineDivisors

/-! Transfer common-divisor certificates to the generic affine parameter map. -/

noncomputable section
namespace FD56
open Polynomial

theorem polynomialAffineShear_C_C {R σ : Type*} [CommRing R] (c : R) :
    polynomialAffineShear (C (MvPolynomial.C c : MvPolynomial (σ ⊕ σ) R)) =
      C (MvPolynomial.C c) := by
  have hs : polynomialVariableSwap (C (MvPolynomial.C c : MvPolynomial (σ ⊕ σ) R)) =
      MvPolynomial.C (C c) := by
    change MvPolynomial.optionEquivRight R (σ ⊕ σ)
      ((MvPolynomial.optionEquivLeft R (σ ⊕ σ)).symm (C (MvPolynomial.C c))) = _
    rw [← MvPolynomial.optionEquivLeft_C, AlgEquiv.symm_apply_apply,
      MvPolynomial.optionEquivRight_C]
  change polynomialVariableSwap.symm
    (affineShear X (polynomialVariableSwap (C (MvPolynomial.C c)))) = _
  rw [hs]
  have hc : affineShear (X : R[X]) (MvPolynomial.C (C c) : MvPolynomial (σ ⊕ σ) R[X]) =
      MvPolynomial.C (C c) := by simp [affineShear, affineShearHom]
  rw [hc, ← hs, RingEquiv.symm_apply_apply]

theorem affineParameterMap_eq_shear (K σ : Type*) [Field K] (p : MvPolynomial σ K) :
    affineParameterMap K σ p =
      (polynomialAffineShear (C (MvPolynomial.rename Sum.inl p))).map
        (algebraMap (MvPolynomial (σ ⊕ σ) K) (AffineCoefficientField K σ)) := by
  let ψ : MvPolynomial σ K →+* (AffineCoefficientField K σ)[X] :=
    (Polynomial.mapRingHom
      (algebraMap (MvPolynomial (σ ⊕ σ) K) (AffineCoefficientField K σ))).comp
      (polynomialAffineShear.toRingHom.comp
        (Polynomial.C.comp (MvPolynomial.rename (Sum.inl : σ → σ ⊕ σ)).toRingHom))
  have he : affineParameterMap K σ = ψ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [ψ, affineParameterMap, polynomialAffineShear_C_C]
    · intro i
      simp [ψ, affineParameterMap, polynomialAffineShear_inl]
  exact RingHom.congr_fun he p

theorem affineParameterMap_common_divisor_isUnit
    {K σ ι : Type*} [Field K] [Fintype σ] (f : ι → MvPolynomial σ K)
    (h : ∀ d, (∀ i, d ∣ f i) → IsUnit d) :
    ∀ d : (AffineCoefficientField K σ)[X],
      (∀ i, d ∣ affineParameterMap K σ (f i)) → IsUnit d := by
  intro d hd
  apply generic_affine_line_common_divisor_isUnit f h d
  intro i
  simpa only [affineParameterMap_eq_shear] using hd i

end FD56
