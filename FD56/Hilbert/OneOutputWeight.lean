/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-! The scalar observability determinant has the triangular row-weight sum. -/

namespace FD56
open scoped BigOperators

def oneOutputWeight (N : ℕ) : ℕ := ∑ i : Fin N, (i.val+1)

theorem oneOutputWeight_twice (N : ℕ) : 2 * oneOutputWeight N = N*(N+1) := by
  induction N with
  | zero => simp [oneOutputWeight]
  | succ N ih =>
    have hs : oneOutputWeight (N+1) = oneOutputWeight N + (N+1) := by
      simp [oneOutputWeight,Fin.sum_univ_castSucc]
    rw [hs]
    nlinarith

theorem oneOutputWeight_eq (N : ℕ) : oneOutputWeight N = N*(N+1)/2 := by
  rw [← oneOutputWeight_twice]
  omega

theorem oneOutputWeight_three_le (N : ℕ) (hN : 2 ≤ N) : 3 ≤ oneOutputWeight N := by
  have h := oneOutputWeight_twice N
  nlinarith

end FD56
