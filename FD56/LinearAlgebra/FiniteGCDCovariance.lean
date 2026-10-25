/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Fintype.Basic

/-! GCD covariance for a finite polynomial family under ring automorphisms. -/

namespace FD56

variable {R ι : Type*} [CommRing R] [IsDomain R] [NormalizedGCDMonoid R] [Fintype ι]

theorem finite_gcd_associated_of_common_divisors (f g : ι → R)
    (h : ∀ d, (∀ i, d ∣ f i) ↔ (∀ i, d ∣ g i)) :
    Associated (Finset.univ.gcd f) (Finset.univ.gcd g) := by
  apply associated_of_dvd_dvd
  · apply Finset.dvd_gcd
    intro i _
    exact (h _).mp (fun j => Finset.gcd_dvd (Finset.mem_univ j)) i
  · apply Finset.dvd_gcd
    intro i _
    exact (h _).mpr (fun j => Finset.gcd_dvd (Finset.mem_univ j)) i

theorem finite_gcd_map_associated (e : R ≃+* R) (f : ι → R) :
    Associated (e (Finset.univ.gcd f)) (Finset.univ.gcd (fun i => e (f i))) := by
  apply associated_of_dvd_dvd
  · apply Finset.dvd_gcd
    intro i _
    exact map_dvd e.toRingHom (Finset.gcd_dvd (Finset.mem_univ i))
  · have hh : e.symm (Finset.univ.gcd (fun i => e (f i))) ∣ Finset.univ.gcd f := by
      apply Finset.dvd_gcd
      intro i _
      have hi := map_dvd e.symm.toRingHom
        (Finset.gcd_dvd (s := Finset.univ) (f := fun i => e (f i)) (Finset.mem_univ i))
      simpa using hi
    simpa using map_dvd e.toRingHom hh

theorem finite_gcd_semi_invariant (e : R ≃+* R) (f : ι → R)
    (h : ∀ d, (∀ i, d ∣ e (f i)) ↔ (∀ i, d ∣ f i)) :
    Associated (e (Finset.univ.gcd f)) (Finset.univ.gcd f) :=
  (finite_gcd_map_associated e f).trans
    (finite_gcd_associated_of_common_divisors (fun i => e (f i)) f h)

end FD56
