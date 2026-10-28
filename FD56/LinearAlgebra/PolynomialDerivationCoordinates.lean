/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PolynomialDerivationImage
import FD56.LinearAlgebra.DerivationIndependentSubfamily

/-! Bounded polynomial variations and their finite coefficient coordinates have
the same differential rank. -/

noncomputable section
namespace FD56
open Polynomial

variable {K L j : Type*} [Field K] [Field L] [Algebra K L]

private def coefficientWindow (W : ℕ) : (j → L[X]) →ₗ[L] (j × Fin (W+1) → L) where
  toFun p i := (p i.1).coeff i.2
  map_add' _ _ := by funext i; exact Polynomial.coeff_add _ _ _
  map_smul' _ _ := by funext i; exact Polynomial.coeff_smul _ _ _

private def derivationCoefficientImage (W : ℕ) (p : j → L[X]) :
    LinearMap.range (polynomialDerivationImageMap (K:=K) p) →ₗ[L]
      LinearMap.range (derivationValuesMap (K:=K)
        (fun i : j × Fin (W+1) => (p i.1).coeff i.2)) :=
  LinearMap.codRestrict _
    ((coefficientWindow W).comp (LinearMap.range
      (polynomialDerivationImageMap (K:=K) p)).subtype)
    (by rintro ⟨_,D,rfl⟩; exact ⟨D,rfl⟩)

private theorem derivationCoefficientImage_bijective (W : ℕ) (p : j → L[X])
    (hp : ∀ i, (p i).natDegree ≤ W) :
    Function.Bijective (derivationCoefficientImage (K:=K) W p) := by
  constructor
  · rintro ⟨u,D,rfl⟩ ⟨v,E,rfl⟩ h
    apply Subtype.ext
    funext i
    apply Polynomial.ext
    intro k
    by_cases hk : k < W+1
    · exact congrFun (congrArg Subtype.val h) (i,⟨k,hk⟩)
    · have hd : (p i).natDegree < k := by have := hp i; omega
      simp only [polynomialDerivationImageMap_coeff,
        Polynomial.coeff_eq_zero_of_natDegree_lt hd,map_zero]
  · rintro ⟨_,D,rfl⟩
    exact ⟨⟨_,D,rfl⟩,rfl⟩

theorem polynomial_derivation_finrank_eq_coefficient_finrank (W : ℕ) (p : j → L[X])
    (hp : ∀ i, (p i).natDegree ≤ W) :
    Module.finrank L (LinearMap.range (polynomialDerivationImageMap (K:=K) p)) =
      Module.finrank L (LinearMap.range (derivationValuesMap (K:=K)
        (fun i : j × Fin (W+1) => (p i.1).coeff i.2))) :=
  (LinearEquiv.ofBijective (derivationCoefficientImage W p)
    (derivationCoefficientImage_bijective W p hp)).finrank_eq

/-- A polynomial differential rank bound supplies faithful specialization of
the coefficient algebra, without selecting independent coordinates by hand. -/
theorem injective_of_polynomial_derivation_rank_bound
    [CharZero K] [Fintype j] {A : Type*} [CommRing A] [IsDomain A] [Algebra K A]
    (φ : A →ₐ[K] L) (p : j → A[X]) (W : ℕ)
    (hp : ∀ i, ((p i).map φ.toRingHom).natDegree ≤ W)
    (htr : Algebra.trdeg K A ≤ (Module.finrank L
      (LinearMap.range (polynomialDerivationImageMap (K:=K)
        (fun i => (p i).map φ.toRingHom))) : Cardinal)) :
    Function.Injective φ := by
  apply injective_of_derivation_rank_bound φ
    (fun i : j × Fin (W+1) => (p i.1).coeff i.2)
  rw [polynomial_derivation_finrank_eq_coefficient_finrank W _ hp] at htr
  have he : (fun i : j × Fin (W+1) => ((p i.1).map φ.toRingHom).coeff i.2) =
      φ ∘ (fun i : j × Fin (W+1) => (p i.1).coeff i.2) := by
    funext i
    exact Polynomial.coeff_map φ.toRingHom i.2
  rw [he] at htr
  exact htr

end FD56
