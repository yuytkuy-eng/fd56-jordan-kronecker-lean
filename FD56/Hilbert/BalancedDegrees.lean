/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericMinimal

/-! Length, sum, and upper bounds for balanced degree lists. -/

namespace FD56
open scoped BigOperators

theorem balancedDegreeList_length (degree count : ℕ) (hc : 0 < count) :
    (balancedDegreeList degree count).length = count := by
  simp only [balancedDegreeList, List.length_append, List.length_replicate]
  have := Nat.mod_lt degree hc
  omega

theorem balancedDegreeList_sum (degree count : ℕ) (hc : 0 < count) :
    (balancedDegreeList degree count).sum = degree := by
  simp only [balancedDegreeList, List.sum_append, List.sum_replicate, smul_eq_mul]
  have hmod := Nat.mod_lt degree hc
  have hdiv := Nat.mod_add_div degree count
  have hsub := Nat.sub_add_cancel hmod.le
  nlinarith

theorem balancedDegreeList_member_le (degree count e : ℕ)
    (he : e ∈ balancedDegreeList degree count) : e ≤ degree / count + 1 := by
  simp only [balancedDegreeList, List.mem_append, List.mem_replicate] at he
  rcases he with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega

theorem balancedDegreeList_ofFn_properties {k : ℕ} (a : Fin k → ℕ)
    (degree count : ℕ) (hc : 0 < count)
    (ha : (List.ofFn a).Perm (balancedDegreeList degree count)) :
    k = count ∧ (∑ i, a i) = degree ∧ ∀ i, a i ≤ degree / count + 1 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [List.length_ofFn, balancedDegreeList_length degree count hc] using ha.length_eq
  · have hh := ha.sum_eq
    simpa only [List.sum_ofFn, balancedDegreeList_sum degree count hc] using hh
  · intro i
    apply balancedDegreeList_member_le
    exact ha.mem_iff.mp (List.mem_ofFn.mpr ⟨i, rfl⟩)

end FD56
