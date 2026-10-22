/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic

/-! Dimension counts for sums of rectangular blocks of two adjacent lengths. -/

namespace FD56

theorem rectangular_balanced_hilbert (q r t d : ℕ) :
    r * (d + 1 - (q + 1)) + t * (d + 1 - q) =
      (r + t) * (d + 1) - (r * (q + 1) + t * q) := by
  by_cases hd : d + 1 ≤ q
  · have htotal : (r + t) * (d + 1) ≤ r * (q + 1) + t * q := by
      nlinarith [Nat.mul_le_mul_left (r + t) hd]
    simp [Nat.sub_eq_zero_of_le hd,
      Nat.sub_eq_zero_of_le (by omega : d + 1 ≤ q + 1), Nat.sub_eq_zero_of_le htotal]
  · have hlong := Nat.sub_add_cancel (by omega : q + 1 ≤ d + 1)
    have hshort := Nat.sub_add_cancel (by omega : q ≤ d + 1)
    have he : r * (d + 1 - (q + 1)) + t * (d + 1 - q) +
        (r * (q + 1) + t * q) = (r + t) * (d + 1) := by
      nlinarith
    omega

theorem rectangular_balanced_rows (n s : ℕ) (hs : 0 < s) :
    n = (n % s) * (n / s + 1) + (s - n % s) * (n / s) := by
  have hdiv := Nat.mod_add_div n s
  have hsub := Nat.sub_add_cancel (Nat.le_of_lt (Nat.mod_lt n hs))
  nlinarith

theorem rectangular_balanced_columns (n s : ℕ) (hs : 0 < s) :
    n + s = (n % s) * (n / s + 2) + (s - n % s) * (n / s + 1) := by
  have hrows := rectangular_balanced_rows n s hs
  have hsub := Nat.sub_add_cancel (Nat.le_of_lt (Nat.mod_lt n hs))
  nlinarith

theorem rectangular_balanced_block_count (n s : ℕ) (hs : 0 < s) :
    n % s + (s - n % s) = s := by
  have := Nat.sub_add_cancel (Nat.le_of_lt (Nat.mod_lt n hs))
  omega

theorem rectangular_balanced_short_count_pos (n s : ℕ) (hs : 0 < s) :
    0 < s - n % s := by
  have := Nat.mod_lt n hs
  omega

theorem rectangular_coefficient_difference (n s d : ℕ) :
    (n + s) * (d + 1) - n * (d + 2) = s * (d + 1) - n := by
  have he : (n + s) * (d + 1) = n * (d + 1) + s * (d + 1) := by ring
  have he' : n * (d + 2) = n * (d + 1) + n := by ring
  omega

theorem rectangular_coefficient_injective_threshold (n s d : ℕ) (hs : 0 < s) :
    (n + s) * (d + 1) ≤ n * (d + 2) ↔ d < n / s := by
  have he : (n + s) * (d + 1) ≤ n * (d + 2) ↔ s * (d + 1) ≤ n := by
    constructor <;> intro h <;> nlinarith
  rw [he, Nat.mul_comm, ← Nat.le_div_iff_mul_le hs]
  omega

theorem rectangular_coefficient_surjective_threshold (n s d : ℕ) :
    n * (d + 2) ≤ (n + s) * (d + 1) ↔ n ≤ s * (d + 1) := by
  constructor <;> intro h <;> nlinarith

theorem rectangular_balanced_hilbert_sizes (n s d : ℕ) (hs : 0 < s) :
    (n % s) * (d + 1 - (n / s + 1)) +
      (s - n % s) * (d + 1 - n / s) = s * (d + 1) - n := by
  rw [rectangular_balanced_hilbert,
    rectangular_balanced_block_count n s hs, ← rectangular_balanced_rows n s hs]

theorem rectangular_balanced_low_degree (q r t d : ℕ)
    (h : (r + t) * (d + 1) < r * (q + 1) + t * q) :
    (∀ i : Fin r ⊕ Fin t,
      d < Sum.elim (fun _ : Fin r => q + 1) (fun _ : Fin t => q) i) ∧
    (∃ i : Fin r ⊕ Fin t,
      d + 1 < Sum.elim (fun _ : Fin r => q + 1) (fun _ : Fin t => q) i) := by
  have hd : d < q := by
    by_contra hnot
    have hq : q ≤ d := by omega
    have hr := Nat.mul_le_mul_left r (Nat.add_le_add_right hq 1)
    have ht := Nat.mul_le_mul_left t (show q ≤ d + 1 by omega)
    nlinarith
  constructor
  · intro i
    cases i <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> omega
  · by_cases hr : 0 < r
    · exact ⟨Sum.inl ⟨0, hr⟩, by simpa using (show d + 1 < q + 1 by omega)⟩
    · have hrzero : r = 0 := by omega
      have ht : 0 < t := by
        by_contra ht
        have htzero : t = 0 := by omega
        simp [hrzero, htzero] at h
      have hq : d + 1 < q := by
        by_contra hnot
        have hh := Nat.mul_le_mul_left t (show q ≤ d + 1 by omega)
        simp only [hrzero, zero_add, zero_mul] at h
        omega
      exact ⟨Sum.inr ⟨0, ht⟩, by simpa using hq⟩

theorem rectangular_sl_hilbert_above (n s d : ℕ) (hn : 0 < n)
    (h : n ≤ s * (d + 1)) :
    n * (s * (d + 1) - n) + (d + 2) =
      (n * s + 1) * (d + 1) - (n * n - 1) := by
  have hsub := Nat.sub_add_cancel h
  have hsquare := Nat.sub_add_cancel (show 1 ≤ n * n by nlinarith)
  have he : n * (s * (d + 1) - n) + (d + 2) + (n * n - 1) =
      (n * s + 1) * (d + 1) := by
    nlinarith
  omega

theorem rectangular_sl_hilbert_below (n s d : ℕ) (hs : 0 < s)
    (h : s * (d + 1) < n) :
    (n * s + 1) * (d + 1) - (n * n - 1) = 0 := by
  have hn : 0 < n := by omega
  have hdegree : d + 2 ≤ n := by
    have hh := Nat.mul_le_mul_right (d + 1) (Nat.succ_le_of_lt hs)
    nlinarith
  have hmul := Nat.mul_le_mul_left n (show s * (d + 1) + 1 ≤ n by omega)
  have hsquare := Nat.sub_add_cancel (show 1 ≤ n * n by nlinarith)
  apply Nat.sub_eq_zero_of_le
  nlinarith

theorem rectangular_sl_hilbert_arithmetic (n s d : ℕ) (hn : 0 < n) (hs : 0 < s) :
    (if n ≤ s * (d + 1) then n * (s * (d + 1) - n) + (d + 2) else 0) =
      (n * s + 1) * (d + 1) - (n * n - 1) := by
  split_ifs with h
  · exact rectangular_sl_hilbert_above n s d hn h
  · exact (rectangular_sl_hilbert_below n s d hs (by omega)).symm

end FD56
