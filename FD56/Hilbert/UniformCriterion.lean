/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MinimalProfile

/-! A vanishing bound, one dimension bound, and an asymptotic slope determine
a uniform list of actual reduced kernel degrees. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

theorem hasMinimalKernelDegrees_replicate_of_bounds
    {K x y : Type*} [Field K] [Fintype y] [DecidableEq y]
    (A : Matrix x y K[X]) (D s C : ℕ) (hD : 0 < D)
    (hzero : Module.finrank K (polynomialKernelAtDegree A (D-1)) = 0)
    (hlower : s ≤ Module.finrank K (polynomialKernelAtDegree A D))
    (hupper : ∀ d, Module.finrank K (polynomialKernelAtDegree A d) ≤ s*(d+1)+C) :
    HasMinimalKernelDegrees A (List.replicate s D) := by
  classical
  obtain ⟨r, B, e, hB, hL, _, hH⟩ := polynomial_kernel_has_minimal_basis A
  have he : ∀ i, D ≤ e i := by
    intro i
    have hi := Finset.single_le_sum (fun j _ => Nat.zero_le (D-1+1-e j))
      (Finset.mem_univ i)
    rw [← hH, hzero] at hi
    omega
  have hcard : r ≤ s := by
    let T := ∑ i, e i
    let d := T+C
    have hi : ∀ i, e i ≤ d+1 := by
      intro i
      have hh := Finset.single_le_sum (fun j _ => Nat.zero_le (e j)) (Finset.mem_univ i)
      dsimp [d,T]
      omega
    have heq : Module.finrank K (polynomialKernelAtDegree A d)+T = r*(d+1) := by
      rw [hH]
      dsimp only [T]
      rw [← Finset.sum_add_distrib]
      simp only [Nat.sub_add_cancel (hi _), Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul]
    have hu := hupper d
    by_contra hh
    have hr : s+1 ≤ r := by omega
    have hm := Nat.mul_le_mul_right (d+1) hr
    dsimp [d] at heq hu hm
    nlinarith
  have hle : ∀ i, D+1-e i ≤ 1 := by intro i; have := he i; omega
  have hsum : (∑ i, (D+1-e i)) = r := by
    have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hle i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      mul_one] at hh
    rw [hH] at hlower
    omega
  have hr : r = s := by rw [hH, hsum] at hlower; omega
  have heq : ∀ i, e i = D := by
    intro i
    have hterm : D+1-e i = 1 := by
      have hh := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
        (fun j (_ : j ∈ Finset.univ) => hle j)).mp
        (by simpa using hsum)
      exact hh i (Finset.mem_univ i)
    have := he i
    omega
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [hH]
  simp [heq, hr]

end FD56
