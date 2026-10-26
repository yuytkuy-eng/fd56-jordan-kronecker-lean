/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.DisjointVariableDivisors

/-! Units after an injective state-coefficient extension contain no output variables. -/

noncomputable section
namespace FD56
open MvPolynomial
variable {K L σ τ : Type*} [Field K] [Field L]

def stateOutputPolynomialEquiv :
    MvPolynomial (σ ⊕ τ) K ≃ₐ[K] MvPolynomial τ (MvPolynomial σ K) :=
  (MvPolynomial.renameEquiv K (Equiv.sumComm σ τ)).trans (MvPolynomial.sumAlgEquiv K τ σ)

theorem stateOutputPolynomialEquiv_C (c : K) :
    stateOutputPolynomialEquiv (σ := σ) (τ := τ) (C c) = C (C c) := by
  simp [stateOutputPolynomialEquiv]

theorem stateOutputPolynomialEquiv_state (i : σ) :
    stateOutputPolynomialEquiv (K := K) (τ := τ) (X (Sum.inl i)) = C (X i) := by
  simp [stateOutputPolynomialEquiv]

theorem stateOutputPolynomialEquiv_output (j : τ) :
    stateOutputPolynomialEquiv (K := K) (σ := σ) (X (Sum.inr j)) = X j := by
  simp [stateOutputPolynomialEquiv]

theorem stateOutputPolynomialEquiv_rename (p : MvPolynomial σ K) :
    stateOutputPolynomialEquiv (τ := τ) (MvPolynomial.rename Sum.inl p) = C p := by
  have h : stateOutputPolynomialEquiv.toRingEquiv.toRingHom.comp
      (MvPolynomial.rename (Sum.inl : σ → σ ⊕ τ)).toRingHom =
      (C : MvPolynomial σ K →+* MvPolynomial τ (MvPolynomial σ K)) := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp [stateOutputPolynomialEquiv_C]
    · intro i; simp [stateOutputPolynomialEquiv_state]
  exact RingHom.congr_fun h p

def stateCoefficientMap (φ : MvPolynomial σ K →+* L) :
    MvPolynomial (σ ⊕ τ) K →+* MvPolynomial τ L :=
  (MvPolynomial.map φ).comp stateOutputPolynomialEquiv.toRingEquiv.toRingHom

theorem stateCoefficientMap_C (φ : MvPolynomial σ K →+* L) (c : K) :
    stateCoefficientMap (τ := τ) φ (C c) = C (φ (C c)) := by
  simp [stateCoefficientMap,stateOutputPolynomialEquiv_C]

theorem stateCoefficientMap_state (φ : MvPolynomial σ K →+* L) (i : σ) :
    stateCoefficientMap (τ := τ) φ (X (Sum.inl i)) = C (φ (X i)) := by
  simp [stateCoefficientMap,stateOutputPolynomialEquiv_state]

theorem stateCoefficientMap_output (φ : MvPolynomial σ K →+* L) (j : τ) :
    stateCoefficientMap φ (X (Sum.inr j)) = X j := by
  simp [stateCoefficientMap,stateOutputPolynomialEquiv_output]

theorem stateCoefficientMap_injective (φ : MvPolynomial σ K →+* L)
    (hφ : Function.Injective φ) : Function.Injective (stateCoefficientMap (τ := τ) φ) :=
  (MvPolynomial.map_injective φ hφ).comp stateOutputPolynomialEquiv.injective

theorem mvPolynomial_eq_C_of_isUnit (p : MvPolynomial τ L) (hp : IsUnit p) :
    p = C (p.coeff 0) := by
  by_contra h
  obtain ⟨j,hj⟩ := exists_positive_degree_of_not_constant p h
  have hle := mvPolynomial_degreeOf_le_of_dvd j
    (show p ∣ (1 : MvPolynomial τ L) from hp.dvd) one_ne_zero
  rw [← MvPolynomial.C_1,MvPolynomial.degreeOf_C] at hle
  exact (Nat.not_lt_of_ge hle) hj

theorem stateCoefficientMap_isUnit_implies_state_only (φ : MvPolynomial σ K →+* L)
    (hφ : Function.Injective φ) (g : MvPolynomial (σ ⊕ τ) K)
    (hg : IsUnit (stateCoefficientMap φ g)) :
    ∃ d : MvPolynomial σ K, g = MvPolynomial.rename Sum.inl d := by
  let p := stateOutputPolynomialEquiv g
  have hc : MvPolynomial.map φ p = C (φ (p.coeff 0)) := by
    simpa only [stateCoefficientMap,RingHom.comp_apply,MvPolynomial.coeff_map] using
      mvPolynomial_eq_C_of_isUnit (stateCoefficientMap φ g) hg
  have hp : p = C (p.coeff 0) := (MvPolynomial.map_injective φ hφ) (by simpa using hc)
  refine ⟨p.coeff 0,?_⟩
  apply stateOutputPolynomialEquiv.injective
  rw [stateOutputPolynomialEquiv_rename]
  exact hp

end FD56
