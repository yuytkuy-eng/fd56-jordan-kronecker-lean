/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.RingTheory.Polynomial.GaussLemma

/-! Descent of primitive polynomial divisors from a coefficient fraction field. -/

namespace FD56
open Polynomial IsLocalization
open scoped nonZeroDivisors

variable {R K : Type*} [CommRing R] [IsDomain R] [NormalizedGCDMonoid R]
  [Field K] [Algebra R K] [IsFractionRing R K]

theorem primitive_dvd_of_fraction_map_dvd {p q : R[X]} (hp : p.IsPrimitive)
    (h : p.map (algebraMap R K) ∣ q.map (algebraMap R K)) : p ∣ q := by
  by_cases hq : q = 0
  · simp [hq]
  obtain ⟨r, hr⟩ := h
  obtain ⟨⟨s, hs⟩, he⟩ := integerNormalization_map_to_map R⁰ r
  have hs0 : s ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hs
  rw [Subtype.coe_mk, Algebra.smul_def, algebraMap_apply] at he
  have hdiv : p ∣ q * C s := by
    refine ⟨integerNormalization R⁰ r, ?_⟩
    apply map_injective (algebraMap R K) (IsFractionRing.injective R K)
    rw [Polynomial.map_mul, Polynomial.map_mul, he, hr, mul_assoc, mul_comm r]
    simp
  have hqs : q * C s ≠ 0 := mul_ne_zero hq (by simpa using hs0)
  rw [← hp.dvd_primPart_iff_dvd hqs, primPart_mul hqs] at hdiv
  have hpart : p ∣ q.primPart := (isUnit_primPart_C s).dvd_mul_right.mp hdiv
  exact (hp.dvd_primPart_iff_dvd hq).mp hpart

/-- Passing to the coefficient fraction field creates no common nonunit divisor. -/
theorem polynomial_common_divisor_isUnit_fraction_map {ι : Type*} (f : ι → R[X])
    (h : ∀ d, (∀ i, d ∣ f i) → IsUnit d) :
    ∀ d : K[X], (∀ i, d ∣ (f i).map (algebraMap R K)) → IsUnit d := by
  intro d hd
  have hd0 : d ≠ 0 := by
    intro hz
    have hf : ∀ i, f i = 0 := by
      intro i
      have he : (f i).map (algebraMap R K) = 0 := by simpa [hz] using hd i
      exact (map_injective (algebraMap R K) (IsFractionRing.injective R K)) (by simpa using he)
    exact not_isUnit_zero (h 0 (fun i => by simp [hf i]))
  let g := integerNormalization R⁰ d
  have hgd : g.primPart.map (algebraMap R K) ∣ d := by
    have hh := map_dvd (mapRingHom (algebraMap R K)) g.primPart_dvd
    obtain ⟨⟨s, hs⟩, he⟩ := integerNormalization_map_to_map R⁰ d
    have hs0 : s ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hs
    rw [Subtype.coe_mk, Algebra.smul_def, algebraMap_apply] at he
    change g.primPart.map (algebraMap R K) ∣ g.map (algebraMap R K) at hh
    rw [show g.map (algebraMap R K) = C (algebraMap R K s) * d from he] at hh
    have hu : IsUnit (C (algebraMap R K s) : K[X]) :=
      (isUnit_iff_ne_zero.mpr (by simpa using (IsFractionRing.injective R K).ne hs0)).map C
    exact hu.dvd_mul_left.mp hh
  apply isUnit_or_eq_zero_of_isUnit_integerNormalization_primPart (R := R) hd0
  exact h g.primPart (fun i => primitive_dvd_of_fraction_map_dvd g.isPrimitive_primPart
    (hgd.trans (hd i)))

end FD56
