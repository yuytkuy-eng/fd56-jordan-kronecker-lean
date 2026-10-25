/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.NonconstantCoordinate
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.RingTheory.Polynomial.Basic

/-! A family omitting every variable has only unit common divisors. -/

namespace FD56
open MvPolynomial

theorem mvPolynomial_degreeOf_le_of_dvd {R σ : Type*} [CommRing R] [IsDomain R]
    (j : σ) {p q : MvPolynomial σ R} (hd : p ∣ q) (hq : q ≠ 0) :
    p.degreeOf j ≤ q.degreeOf j := by
  let e := coordinatePolynomialEquiv (R := R) j
  have he : e q ≠ 0 := by
    intro hz
    apply hq
    apply e.injective
    simpa only [map_zero] using hz
  have hd' : e p ∣ e q := map_dvd e.toRingHom hd
  simpa only [e, coordinatePolynomialEquiv_natDegree] using
    Polynomial.natDegree_le_of_dvd hd' he

theorem common_divisor_isUnit_of_variable_omissions {K σ ι : Type*} [Field K]
    (f : ι → MvPolynomial σ K) (hnonzero : ∃ i, f i ≠ 0)
    (homit : ∀ j, ∃ i, f i ≠ 0 ∧ (f i).degreeOf j = 0)
    (p : MvPolynomial σ K) (hd : ∀ i, p ∣ f i) : IsUnit p := by
  classical
  have hp : p ≠ 0 := by
    obtain ⟨i, hi⟩ := hnonzero
    intro hz
    have hh := hd i
    rw [hz, zero_dvd_iff] at hh
    exact hi hh
  by_contra hu
  obtain ⟨j, hj⟩ := exists_positive_degree_of_nonzero_nonunit p hp hu
  obtain ⟨i, hi, hzero⟩ := homit j
  have hle := mvPolynomial_degreeOf_le_of_dvd j (hd i) hi
  rw [hzero] at hle
  exact (Nat.not_lt_of_ge hle) hj

end FD56
