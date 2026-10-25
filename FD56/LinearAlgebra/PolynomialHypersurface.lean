/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! A positive-degree polynomial relation does not identify distinct coefficients. -/

namespace FD56
open Polynomial
variable {R : Type*} [CommRing R] [IsDomain R]

theorem polynomial_quotient_coefficients_injective (g : R[X]) (hg : 0 < g.natDegree) :
    Function.Injective ((Ideal.Quotient.mk (Ideal.span ({g} : Set R[X]))).comp C) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  have hm : C a ∈ Ideal.span ({g} : Set R[X]) := Ideal.Quotient.eq_zero_iff_mem.mp ha
  have hd : g ∣ C a := Ideal.mem_span_singleton.mp hm
  by_contra hn
  have hdegree := natDegree_le_of_dvd hd (show C a ≠ 0 by simpa using hn)
  have : g.natDegree = 0 := Nat.eq_zero_of_le_zero (by simpa using hdegree)
  exact (Nat.ne_of_gt hg) this

end FD56
