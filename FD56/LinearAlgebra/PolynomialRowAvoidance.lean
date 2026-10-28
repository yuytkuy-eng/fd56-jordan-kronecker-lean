/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PolynomialMatrix
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.Data.Set.Finite.Lattice

/-! A primitive pair of polynomial rows with nonzero determinant has only
finitely many constant combinations whose two entries fail to be coprime. -/

namespace FD56
open Polynomial

variable {K : Type*} [Field K]

private theorem row_common_factor_constants_subsingleton
    (f₀ f₁ g₀ g₁ p : K[X]) (hp : ¬IsUnit p)
    (hjoint : ∀ d : K[X], d∣f₀ → d∣f₁ → d∣g₀ → d∣g₁ → IsUnit d) :
    {t : K | p∣f₀+C t*g₀ ∧ p∣f₁+C t*g₁}.Subsingleton := by
  intro t ht u hu
  by_contra htu
  have hunit : IsUnit (C (t-u) : K[X]) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr htu))
  have hdivide (f g : K[X]) (ht : p∣f+C t*g) (hu : p∣f+C u*g) : p∣g := by
    apply hunit.dvd_mul_left.mp
    have he : C (t-u)*g=(f+C t*g)-(f+C u*g) := by
      rw [map_sub]
      ring
    rw [he]
    exact dvd_sub ht hu
  have hg₀ : p∣g₀ := hdivide f₀ g₀ ht.1 hu.1
  have hg₁ : p∣g₁ := hdivide f₁ g₁ ht.2 hu.2
  have hf₀ : p∣f₀ := by
    simpa only [add_sub_cancel_right] using
      dvd_sub ht.1 (dvd_mul_of_dvd_right hg₀ (C t))
  have hf₁ : p∣f₁ := by
    simpa only [add_sub_cancel_right] using
      dvd_sub ht.2 (dvd_mul_of_dvd_right hg₁ (C t))
  exact hp (hjoint p hf₀ hf₁ hg₀ hg₁)

theorem finite_non_coprime_constant_row_combinations
    (f₀ f₁ g₀ g₁ : K[X]) (hwedge : f₀*g₁-f₁*g₀≠0)
    (hjoint : ∀ d : K[X], d∣f₀ → d∣f₁ → d∣g₀ → d∣g₁ → IsUnit d) :
    {t : K | ¬IsCoprime (f₀+C t*g₀) (f₁+C t*g₁)}.Finite := by
  classical
  let factors := (UniqueFactorizationMonoid.normalizedFactors (f₀*g₁-f₁*g₀)).toFinset
  let bad (p : K[X]) : Set K := {t | p∣f₀+C t*g₀ ∧ p∣f₁+C t*g₁}
  have hfinite : (⋃ p ∈ (factors : Set K[X]), bad p).Finite := by
    apply factors.finite_toSet.biUnion
    intro p hp
    have hirr : Irreducible p := UniqueFactorizationMonoid.irreducible_of_normalized_factor
      p (Multiset.mem_toFinset.mp hp)
    exact (row_common_factor_constants_subsingleton f₀ f₁ g₀ g₁ p hirr.not_isUnit hjoint).finite
  apply hfinite.subset
  intro t ht
  by_contra hbad
  apply ht
  have he : (f₀+C t*g₀)*g₁-(f₁+C t*g₁)*g₀=f₀*g₁-f₁*g₀ := by ring
  apply isCoprime_of_irreducible_dvd
  · rintro ⟨h₀,h₁⟩
    apply hwedge
    rw [← he,h₀,h₁]
    ring
  · intro p hp hp₀ hp₁
    have hpdvd : p∣f₀*g₁-f₁*g₀ := by
      rw [← he]
      exact dvd_sub (dvd_mul_of_dvd_left hp₀ g₁) (dvd_mul_of_dvd_left hp₁ g₀)
    obtain ⟨d,hd,hpd⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd
      hwedge hp hpdvd
    apply hbad
    apply Set.mem_iUnion.mpr
    refine ⟨d,Set.mem_iUnion.mpr ⟨?_,?_⟩⟩
    · exact Multiset.mem_toFinset.mpr hd
    · exact ⟨hpd.dvd_iff_dvd_left.mp hp₀,hpd.dvd_iff_dvd_left.mp hp₁⟩

theorem exists_coprime_constant_row_combination [Infinite K]
    (f₀ f₁ g₀ g₁ : K[X]) (hwedge : f₀*g₁-f₁*g₀≠0)
    (hjoint : ∀ d : K[X], d∣f₀ → d∣f₁ → d∣g₀ → d∣g₁ → IsUnit d) :
    ∃ t : K, IsCoprime (f₀+C t*g₀) (f₁+C t*g₁) := by
  obtain ⟨t,ht⟩ := (finite_non_coprime_constant_row_combinations
    f₀ f₁ g₀ g₁ hwedge hjoint).exists_not_mem
  exact ⟨t,not_not.mp ht⟩

end FD56
