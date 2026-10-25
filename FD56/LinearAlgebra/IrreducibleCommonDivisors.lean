/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
import Mathlib.Algebra.GCDMonoid.Finset

/-! Excluding irreducible common divisors proves that a nonzero gcd is a unit. -/

namespace FD56

variable {R ι : Type*}

section Factorization

variable [CommMonoidWithZero R] [WfDvdMonoid R]

theorem isUnit_of_nonzero_common_divisor_of_no_irreducible_common_divisor
    (f : ι → R) (hirr : ∀ p : R, Irreducible p → ¬∀ i, p ∣ f i)
    {d : R} (hd0 : d ≠ 0) (hd : ∀ i, d ∣ f i) : IsUnit d := by
  by_contra hu
  obtain ⟨p, hp, hpd⟩ := WfDvdMonoid.exists_irreducible_factor hu hd0
  exact hirr p hp (fun i => hpd.trans (hd i))

/-- A nonzero family member rules out zero as a common divisor. -/
theorem isUnit_of_common_divisor_of_no_irreducible_common_divisor
    (f : ι → R) (h0 : ∃ i, f i ≠ 0)
    (hirr : ∀ p : R, Irreducible p → ¬∀ i, p ∣ f i)
    {d : R} (hd : ∀ i, d ∣ f i) : IsUnit d := by
  obtain ⟨i, hi⟩ := h0
  exact isUnit_of_nonzero_common_divisor_of_no_irreducible_common_divisor f hirr
    (ne_zero_of_dvd_ne_zero hi (hd i)) hd

end Factorization

section FiniteGCD

variable [CancelCommMonoidWithZero R] [NormalizedGCDMonoid R] [WfDvdMonoid R]

theorem isUnit_finset_gcd_of_no_irreducible_common_divisor
    (s : Finset ι) (f : ι → R) (h0 : ∃ i ∈ s, f i ≠ 0)
    (hirr : ∀ p : R, Irreducible p → ¬∀ i ∈ s, p ∣ f i) :
    IsUnit (s.gcd f) := by
  apply isUnit_of_common_divisor_of_no_irreducible_common_divisor (fun i : s => f i.val)
  · obtain ⟨i, hi, hfi⟩ := h0
    exact ⟨⟨i, hi⟩, hfi⟩
  · intro p hp hd
    exact hirr p hp (fun i hi => hd ⟨i, hi⟩)
  · intro i
    exact Finset.gcd_dvd i.property

theorem finset_gcd_eq_one_of_no_irreducible_common_divisor
    (s : Finset ι) (f : ι → R) (h0 : ∃ i ∈ s, f i ≠ 0)
    (hirr : ∀ p : R, Irreducible p → ¬∀ i ∈ s, p ∣ f i) :
    s.gcd f = 1 := by
  have h := normalize_eq_one.mpr
    (isUnit_finset_gcd_of_no_irreducible_common_divisor s f h0 hirr)
  simpa only [Finset.normalize_gcd] using h

end FiniteGCD
end FD56
