/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.LowDepthGLDimension

/-! An eventual scalar Hilbert contribution determines the change in block dimension. -/

namespace FD56

theorem degreeList_hilbert_add_sum (xs : List ℕ) (d : ℕ) (h : xs.sum ≤ d+1) :
    (xs.map (fun e => d+1-e)).sum + xs.sum = xs.length*(d+1) := by
  induction xs with
  | nil => simp
  | cons e xs ih =>
    have he : e ≤ d+1 := by simp only [List.sum_cons] at h; omega
    have hx : xs.sum ≤ d+1 := by simp only [List.sum_cons] at h; omega
    have ht := ih hx
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, one_mul]
    omega

theorem eventual_hilbert_scalar_profile (xs ys : List ℕ) (N : ℕ)
    (h : ∀ d, N ≤ d → (ys.map (fun e => d+1-e)).sum =
      (xs.map (fun e => d+1-e)).sum + (d+2)) :
    ys.length = xs.length+1 ∧ ys.sum+1 = xs.sum := by
  let d := N+xs.sum+ys.sum
  have hx0 := degreeList_hilbert_add_sum xs d (by dsimp [d]; omega)
  have hy0 := degreeList_hilbert_add_sum ys d (by dsimp [d]; omega)
  have hx1 := degreeList_hilbert_add_sum xs (d+1) (by dsimp [d]; omega)
  have hy1 := degreeList_hilbert_add_sum ys (d+1) (by dsimp [d]; omega)
  have h0 := h d (by dsimp [d]; omega)
  have h1 := h (d+1) (by dsimp [d]; omega)
  have hlen : ys.length = xs.length+1 := by nlinarith
  refine ⟨hlen, ?_⟩
  rw [hlen] at hy0
  nlinarith

theorem eventual_hilbert_scalar_block_dimension (xs ys : List ℕ) (N : ℕ)
    (h : ∀ d, N ≤ d → (ys.map (fun e => d+1-e)).sum =
      (xs.map (fun e => d+1-e)).sum + (d+2)) :
    (ys.map (fun e => 2*e+1)).sum+1 = (xs.map (fun e => 2*e+1)).sum := by
  obtain ⟨hl, hs⟩ := eventual_hilbert_scalar_profile xs ys N h
  rw [nat_list_affine_sum, nat_list_affine_sum]
  simp only [one_mul]
  omega

end FD56
