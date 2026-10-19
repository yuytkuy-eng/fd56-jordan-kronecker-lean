/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic

/-! A finite nonnegative minimal-index list is uniquely determined by its
Hilbert function. The second finite difference recovers each multiplicity. -/

namespace FD56

def listHilbert (xs : List ℕ) (d : ℤ) : ℤ :=
  (xs.map (fun e : ℕ => max 0 (d + 1 - (e : ℤ)))).sum

theorem hilbert_atom_second_difference (e n : ℕ) :
    max 0 ((n : ℤ) + 1 - e) - 2 * max 0 ((n : ℤ) - e) +
      max 0 ((n : ℤ) - 1 - e) = if e = n then 1 else 0 := by
  split_ifs with h
  · subst e
    simp
  · by_cases hlt : e < n
    · rw [max_eq_right (by omega : 0 ≤ (n : ℤ) + 1 - e),
        max_eq_right (by omega : 0 ≤ (n : ℤ) - e),
        max_eq_right (by omega : 0 ≤ (n : ℤ) - 1 - e)]
      ring
    · rw [max_eq_left (by omega : (n : ℤ) + 1 - e ≤ 0),
        max_eq_left (by omega : (n : ℤ) - e ≤ 0),
        max_eq_left (by omega : (n : ℤ) - 1 - e ≤ 0)]
      norm_num

theorem listHilbert_second_difference (xs : List ℕ) (n : ℕ) :
    listHilbert xs n - 2 * listHilbert xs ((n : ℤ) - 1) +
      listHilbert xs ((n : ℤ) - 2) = (xs.count n : ℤ) := by
  induction xs with
  | nil => simp [listHilbert]
  | cons e xs ih =>
    have hatom := hilbert_atom_second_difference e n
    simp only [listHilbert, List.map_cons, List.sum_cons] at ih ⊢
    have h1 : (n : ℤ) - 1 + 1 = n := by omega
    have h2 : (n : ℤ) - 2 + 1 = (n : ℤ) - 1 := by omega
    rw [h1, h2] at ih ⊢
    by_cases he : e = n
    · subst e
      simp only [ite_true] at hatom
      simp only [List.count_cons_self, Nat.cast_add, Nat.cast_one]
      linear_combination ih + hatom
    · simp only [if_neg he] at hatom
      simp only [List.count_cons_of_ne he]
      linear_combination ih + hatom

theorem listHilbert_negative (xs : List ℕ) (d : ℤ) (hd : d < 0) :
    listHilbert xs d = 0 := by
  induction xs with
  | nil => simp [listHilbert]
  | cons e xs ih =>
    change max 0 (d + 1 - (e : ℤ)) + listHilbert xs d = 0
    rw [max_eq_left (by omega), ih, add_zero]

/-- Equality at nonnegative degrees suffices; negative degrees vanish. -/
theorem listHilbert_determines_indices (xs ys : List ℕ)
    (h : ∀ d : ℕ, listHilbert xs d = listHilbert ys d) : xs.Perm ys := by
  have hall : ∀ d : ℤ, listHilbert xs d = listHilbert ys d := by
    intro d
    by_cases hd : 0 ≤ d
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hd
      exact h n
    · rw [listHilbert_negative xs d (by omega), listHilbert_negative ys d (by omega)]
  apply List.perm_iff_count.mpr
  intro n
  have hx := listHilbert_second_difference xs n
  have hy := listHilbert_second_difference ys n
  rw [hall, hall, hall] at hx
  exact_mod_cast hx.symm.trans hy

end FD56
