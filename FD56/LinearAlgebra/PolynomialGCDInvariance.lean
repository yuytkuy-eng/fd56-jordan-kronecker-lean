/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PolynomialCommonDivisors
import Mathlib.Algebra.GroupWithZero.Associated
import FD56.LinearAlgebra.FiniteGCDCovariance

namespace FD56
open Polynomial
variable {R : Type*} [CommRing R] [IsDomain R]

theorem associated_constant_eq_of_eval_zero {p : R[X]} {g : R}
    (h : Associated p (C g)) (he : p.eval 0 = g) : p = C g := by
  by_cases hg : g = 0
  · have hp : p = 0 := by simpa [hg] using h.dvd'
    simp [hp, hg]
  have hd : p.natDegree = 0 := Nat.eq_zero_of_le_zero (by
    simpa using natDegree_le_of_dvd h.dvd (by simpa using hg))
  rw [eq_C_of_natDegree_eq_zero hd, coeff_zero_eq_eval_zero, he]

theorem finite_gcd_constants_associated {ι : Type*} [Fintype ι]
    [NormalizedGCDMonoid R] [NormalizedGCDMonoid R[X]] (f : ι → R) :
    Associated (C (Finset.univ.gcd f)) (Finset.univ.gcd (fun i => C (f i))) := by
  apply associated_of_dvd_dvd
  · apply Finset.dvd_gcd
    intro i _
    exact map_dvd C (Finset.gcd_dvd (Finset.mem_univ i))
  · by_cases hex : ∃ i, f i ≠ 0
    · obtain ⟨i, hi⟩ := hex
      let p : R[X] := Finset.univ.gcd (fun i => C (f i))
      have hp (j) : p ∣ C (f j) := Finset.gcd_dvd (Finset.mem_univ j)
      have hd : p.natDegree = 0 := Nat.eq_zero_of_le_zero (by
        simpa using natDegree_le_of_dvd (hp i) (by simpa using hi))
      have hh : p.eval 0 ∣ Finset.univ.gcd f := by
        apply Finset.dvd_gcd
        intro j _
        simpa using map_dvd (evalRingHom (0 : R)) (hp j)
      have he : p = C (p.eval 0) := by
        exact (eq_C_of_natDegree_eq_zero hd).trans (congrArg C (coeff_zero_eq_eval_zero p))
      change p ∣ C (Finset.univ.gcd f)
      rw [he]
      exact map_dvd C hh
    · have hf : ∀ i, f i = 0 := by simpa using hex
      have hg : Finset.univ.gcd f = 0 := Finset.gcd_eq_zero_iff.mpr (fun i _ => hf i)
      simp [hg]

theorem finite_gcd_parameter_invariant {ι : Type*} [Fintype ι]
    [NormalizedGCDMonoid R] [NormalizedGCDMonoid R[X]] (f : ι → R)
    (e : R[X] ≃+* R[X])
    (h : ∀ d, (∀ i, d ∣ e (C (f i))) ↔ (∀ i, d ∣ C (f i)))
    (hzero : ∀ a : R, (e (C a)).eval 0 = a) :
    e (C (Finset.univ.gcd f)) = C (Finset.univ.gcd f) := by
  have ha := finite_gcd_constants_associated f
  have hb : Associated (e (C (Finset.univ.gcd f)))
      (e (Finset.univ.gcd (fun i => C (f i)))) :=
    associated_of_dvd_dvd (map_dvd e.toRingHom ha.dvd) (map_dvd e.toRingHom ha.dvd')
  have hc := finite_gcd_semi_invariant e (fun i => C (f i)) h
  exact associated_constant_eq_of_eval_zero (hb.trans (hc.trans ha.symm)) (hzero _)

end FD56
