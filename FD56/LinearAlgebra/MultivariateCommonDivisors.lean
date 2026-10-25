/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PolynomialCommonDivisors
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Polynomial.Basic

/-! A finite independent variable family preserves common-divisor triviality. -/

namespace FD56
open MvPolynomial
variable {R ι : Type*} [CommRing R] [IsDomain R]

theorem finite_variable_constants_common_divisor_isUnit (f : ι → R)
    (h : ∀ d, (∀ i, d ∣ f i) → IsUnit d) (n : ℕ) :
    ∀ d : MvPolynomial (Fin n) R, (∀ i, d ∣ C (f i)) → IsUnit d := by
  induction n with
  | zero =>
    intro d hd
    let e := isEmptyAlgEquiv R (Fin 0)
    have hu : IsUnit (e d) := h _ (fun i => by
      simpa [e, finSuccEquiv_apply] using map_dvd e.toRingHom (hd i))
    simpa using hu.map e.symm.toRingHom
  | succ n ih =>
    intro d hd
    let e := finSuccEquiv R n
    have hu : IsUnit (e d) := polynomial_constants_common_divisor_isUnit
      (fun i => (C (f i) : MvPolynomial (Fin n) R)) ih _ (fun i => by
        simpa [e, finSuccEquiv_apply] using map_dvd e.toRingHom (hd i))
    simpa using hu.map e.symm.toRingHom

theorem multivariate_constants_common_divisor_isUnit {σ : Type*} [Fintype σ]
    (f : ι → R) (h : ∀ d, (∀ i, d ∣ f i) → IsUnit d) :
    ∀ d : MvPolynomial σ R, (∀ i, d ∣ C (f i)) → IsUnit d := by
  classical
  intro d hd
  let e := renameEquiv R (Fintype.equivFin σ)
  have hu : IsUnit (e d) := finite_variable_constants_common_divisor_isUnit f h _ _
    (fun i => by simpa [e] using map_dvd e.toRingHom (hd i))
  simpa using hu.map e.symm.toRingHom

theorem rename_inl_common_divisor_isUnit {σ τ : Type*} [Fintype τ]
    (f : ι → MvPolynomial σ R)
    (h : ∀ d, (∀ i, d ∣ f i) → IsUnit d) :
    ∀ d : MvPolynomial (σ ⊕ τ) R,
      (∀ i, d ∣ rename Sum.inl (f i)) → IsUnit d := by
  classical
  let e := (renameEquiv R (Equiv.sumComm σ τ)).trans (sumAlgEquiv R τ σ)
  have he : e.toAlgHom.comp (rename Sum.inl) =
      IsScalarTower.toAlgHom R (MvPolynomial σ R) (MvPolynomial τ (MvPolynomial σ R)) := by
    ext i
    simp [e]
  intro d hd
  have hu : IsUnit (e d) := multivariate_constants_common_divisor_isUnit f h _ (fun i => by
    have hh := map_dvd e.toRingHom (hd i)
    have hv := DFunLike.congr_fun he (f i)
    change e (rename Sum.inl (f i)) = C (f i) at hv
    change e d ∣ e (rename Sum.inl (f i)) at hh
    rwa [hv] at hh)
  simpa using hu.map e.symm.toRingHom

end FD56
