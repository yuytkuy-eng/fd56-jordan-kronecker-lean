/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericMinimal

/-! Adjacent degree lists have the balanced Hilbert function. -/

namespace FD56

theorem adjacent_degree_hilbert (x y b d : ℕ) :
    x * (d + 1 - b) + y * (d + 1 - (b + 1)) =
      (x + y) * (d + 1) - (b * (x + y) + y) := by
  by_cases hd : d + 1 ≤ b
  · have h0 : d + 1 - b = 0 := by omega
    have h1 : d + 1 - (b + 1) = 0 := by omega
    have hh : (x + y) * (d + 1) ≤ b * (x + y) + y := by nlinarith
    simp [h0, h1, Nat.sub_eq_zero_of_le hh]
  · have h0 := Nat.sub_add_cancel (show b ≤ d + 1 by omega)
    have h1 := Nat.sub_add_cancel (show b + 1 ≤ d + 1 by omega)
    have hh : b * (x + y) + y ≤ (x + y) * (d + 1) := by nlinarith
    have h2 := Nat.sub_add_cancel hh
    nlinarith

theorem hasMinimalKernelDegrees_balanced_of_adjacent
    {K u v : Type*} [Field K] [Fintype v] [DecidableEq v]
    (A : Matrix u v (Polynomial K)) (x y b : ℕ) (hcount : 0 < x + y)
    (h : HasMinimalKernelDegrees A (List.replicate x b ++ List.replicate y (b + 1))) :
    HasMinimalKernelDegrees A (balancedDegreeList (b * (x + y) + y) (x + y)) := by
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [(hasMinimalKernelDegrees_iff_hilbert _ _).mp h d,
    balancedDegreeList_hilbert _ _ d hcount]
  simpa only [List.map_append, List.map_replicate, List.sum_append,
    List.sum_replicate, smul_eq_mul] using adjacent_degree_hilbert x y b d

end FD56
