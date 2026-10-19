/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic

/-! Two adjacent Hilbert values and the index sum force balanced indices.
The geometric realization of these values is a separate requirement. -/

namespace FD56
open scoped BigOperators

theorem two_degree_tests_force_balanced {ι : Type*} [Fintype ι]
    (e : ι → ℤ) (a u : ℤ)
    (hsum : ∑ i, e i = Fintype.card ι * a + u)
    (hbelow : ∑ i, max 0 (a - e i) = 0)
    (hat : ∑ i, max 0 (a + 1 - e i) = Fintype.card ι - u) :
    ∀ i, a ≤ e i ∧ e i ≤ a + 1 := by
  have hupper : ∑ i, max 0 (e i - a - 1) = 0 := by
    have hrewrite : ∀ i, max 0 (e i - a - 1) =
        (e i - a - 1) + max 0 (a + 1 - e i) := by
      intro i
      omega
    simp_rw [hrewrite]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, hsum, hat]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  intro i
  have hl := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) =>
    le_max_left (0 : ℤ) (a - e j)) (Finset.mem_univ i)
  have hu := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) =>
    le_max_left (0 : ℤ) (e j - a - 1)) (Finset.mem_univ i)
  rw [hbelow] at hl
  rw [hupper] at hu
  constructor <;> omega

end FD56
