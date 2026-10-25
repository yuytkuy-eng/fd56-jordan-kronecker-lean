/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Eval.Coeff

/-! Common divisors under polynomial extension and coefficient specialization. -/

namespace FD56
open Polynomial

variable {R S ι : Type*} [CommRing R] [IsDomain R]

/-- Adjoining one variable preserves the absence of a common nonunit divisor. -/
theorem polynomial_constants_common_divisor_isUnit (f : ι → R)
    (h : ∀ d, (∀ i, d ∣ f i) → IsUnit d) :
    ∀ d : R[X], (∀ i, d ∣ C (f i)) → IsUnit d := by
  intro d hd
  have hex : ∃ i, f i ≠ 0 := by
    by_contra hn
    have hz : ∀ i, f i = 0 := by simpa using hn
    have hu := h 0 (fun i => by simp [hz i])
    exact not_isUnit_zero hu
  obtain ⟨i, hi⟩ := hex
  have hdeg : d.natDegree = 0 := Nat.eq_zero_of_le_zero (by
    simpa using natDegree_le_of_dvd (hd i) (by simpa using hi))
  have hu : IsUnit (d.eval 0) := h _ (fun j => by
    simpa using map_dvd (evalRingHom (0 : R)) (hd j))
  rw [eq_C_of_natDegree_eq_zero hdeg]
  simpa only [coeff_zero_eq_eval_zero] using hu.map C

/-- Unit leading coefficients prevent a factor from disappearing under specialization. -/
theorem polynomial_common_divisor_isUnit_of_specialization
    [CommRing S] [IsDomain S] (φ : R →+* S) (f : ι → R[X])
    (hlead : ∀ a, (∀ i, a ∣ (f i).leadingCoeff) → IsUnit a)
    (hspecial : ∃ i, IsUnit ((f i).map φ)) :
    ∀ d, (∀ i, d ∣ f i) → IsUnit d := by
  intro d hd
  apply isUnit_of_isUnit_leadingCoeff_of_isUnit_map φ
  · exact hlead _ (fun i => leadingCoeff_dvd_leadingCoeff (hd i))
  · obtain ⟨i, hi⟩ := hspecial
    exact isUnit_of_dvd_unit (map_dvd (mapRingHom φ) (hd i)) hi

end FD56
