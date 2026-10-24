/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.AdjacentCriterion
import FD56.Hilbert.AdjacentDegrees
import FD56.Hilbert.MixedOneThreeBounds

/-! Two scalar bounds determine the three-high-column SL profile. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem generic_mixed_one_three_glHilbert (u : ℕ) (hu : 0<u)
    (hm : Fintype.card m=u+6) (hn : Fintype.card n=2*u+9) (d : ℕ) :
    Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (polynomialKernelAtDegree (glEquationMatrix
        (genericAffineSquare K n m) (genericAffineRows K n m)) d) =
      3*u*(d+1-(u+6))+9*(d+1-(u+7)) := by
  have hG := (hasMinimalKernelDegrees_iff_hilbert _ _).mp
    (generic_middle_gl_minimal_degrees (K := K) (n := n) (m := m) (by omega) (by omega)) d
  have hr : Fintype.card n-Fintype.card m=u+3 := by omega
  have hs : Fintype.card m-(Fintype.card n-Fintype.card m)=3 := by omega
  have ha : (u+6)/(u+3)=1 := by apply Nat.div_eq_of_lt_le <;> omega
  have ham : (u+6)%(u+3)=3 := by rw [Nat.mod_eq_sub_mul_div,ha]; omega
  have hb : (u+6+2*(u+3))/3=u+4 := by omega
  have hbm : (u+6+2*(u+3))%3=0 := by omega
  rw [hs,hr,hm] at hG
  rw [hG]
  simp only [balancedDegreeList,ha,ham,hb,hbm,Nat.sub_zero,
    show u+3-3=u by omega,List.replicate_zero,List.nil_append,Nat.reduceAdd,
    degreeConvolution,List.map_flatMap,nat_sum_flatMap,List.map_append,List.map_replicate,
    List.map_map,List.sum_append,List.sum_replicate,smul_eq_mul,Function.comp_apply,
    show 1+(u+4)+1=u+6 by omega,show 2+(u+4)+1=u+7 by omega]
  ring

theorem generic_mixed_one_three_slHilbert_later (u : ℕ) (hu : 0<u)
    (hm : Fintype.card m=u+6) (hn : Fintype.card n=2*u+9) (i₀ : n) :
    slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) (u+7)=7*u+18 := by
  have hr : Fintype.card n-Fintype.card m=u+3 := by omega
  have hs : Fintype.card m-(Fintype.card n-Fintype.card m)=3 := by omega
  have ha : (u+6)/(u+3)=1 := by apply Nat.div_eq_of_lt_le <;> omega
  rw [generic_middle_slHilbert_high i₀ (by omega) (by omega) (u+7)
    (by rw [hs,hr,hm,ha]; omega),generic_mixed_one_three_glHilbert u hu hm hn]
  have h0 : u+7+1-(u+6)=2 := by omega
  have h1 : u+7+1-(u+7)=1 := by omega
  rw [h0,h1]
  ring

theorem generic_mixed_one_three_sl_minimal_degrees_of_bounds (u : ℕ) (hu : 2≤u)
    (hm : Fintype.card m=u+6) (hn : Fintype.card n=2*u+9) (i₀ : n)
    (hzero : slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) (u+4)=0)
    (hupper : slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) (u+5)≤u-2) :
    HasMinimalKernelDegrees (slEquationMatrix (genericAffineSquare K n m)
      (genericAffineRows K n m) i₀)
      (List.replicate (u-2) (u+5) ++ List.replicate (2*u+12) (u+6)) := by
  have hsub : u-2+2=u := Nat.sub_add_cancel hu
  apply hasMinimalKernelDegrees_adjacent_of_bounds _ (u+5) (u-2) (2*u+12) 1 (by omega)
  · rw [← slHilbert_eq_matrix_kernel _ _ i₀]
    simpa only [show u+5-1=u+4 by omega] using hzero
  · rw [← slHilbert_eq_matrix_kernel _ _ i₀]
    exact Nat.le_antisymm hupper (generic_mixed_one_three_slHilbert_critical_lower u hu hm hn i₀)
  · rw [← slHilbert_eq_matrix_kernel _ _ i₀]
    have hh := generic_mixed_one_three_slHilbert_later (K := K) u (by omega) hm hn i₀
    simpa only [Nat.add_assoc,Nat.reduceAdd] using (show 3*(u-2)+2*(2*u+12)≤
      slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) (u+7) by rw [hh]; omega)
  · intro d
    rw [← slHilbert_eq_matrix_kernel _ _ i₀]
    have hh := (generic_middle_slHilbert_bounds (K := K) (n := n) (m := m)
      i₀ (by omega) (by omega) d).2
    rw [generic_mixed_one_three_glHilbert u (by omega) hm hn] at hh
    have h0 := Nat.mul_le_mul_left (3*u) (Nat.sub_le (d+1) (u+6))
    have h1 := Nat.mul_le_mul_left 9 (Nat.sub_le (d+1) (u+7))
    nlinarith

theorem generic_mixed_one_three_sl_balanced_of_bounds (u : ℕ) (hu : 2≤u)
    (hm : Fintype.card m=u+6) (hn : Fintype.card n=2*u+9) (i₀ : n)
    (hzero : slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) (u+4)=0)
    (hupper : slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) (u+5)≤u-2) :
    HasMinimalKernelDegrees (slEquationMatrix (genericAffineSquare K n m)
      (genericAffineRows K n m) i₀)
      (balancedDegreeList (3*u^2+27*u+62) (3*u+10)) := by
  have hh := generic_mixed_one_three_sl_minimal_degrees_of_bounds u hu hm hn i₀ hzero hupper
  have hb := hasMinimalKernelDegrees_balanced_of_adjacent _ (u-2) (2*u+12) (u+5)
    (by omega) (by simpa only [Nat.add_assoc,Nat.reduceAdd] using hh)
  have hsub : u-2+2=u := Nat.sub_add_cancel hu
  have hc : (u-2)+(2*u+12)=3*u+10 := by omega
  have hs : (u+5)*((u-2)+(2*u+12))+(2*u+12)=3*u^2+27*u+62 := by
    rw [hc]
    ring
  rw [hs,hc] at hb
  exact hb

theorem generic_mixed_one_three_small_sl_balanced_of_zero
    (hm : Fintype.card m=7) (hn : Fintype.card n=11) (i₀ : n)
    (hzero : slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) 6=0) :
    HasMinimalKernelDegrees (slEquationMatrix (genericAffineSquare K n m)
      (genericAffineRows K n m) i₀) (balancedDegreeList 92 13) := by
  have hprofile : HasMinimalKernelDegrees (slEquationMatrix (genericAffineSquare K n m)
      (genericAffineRows K n m) i₀) (List.replicate 12 7 ++ List.replicate 1 8) := by
    apply hasMinimalKernelDegrees_adjacent_of_bounds _ 7 12 1 1 (by decide)
    · rw [← slHilbert_eq_matrix_kernel _ _ i₀]
      exact hzero
    · rw [← slHilbert_eq_matrix_kernel _ _ i₀]
      have hl := generic_mixed_one_three_slHilbert_lower (K := K) 1 7
        (by decide) (by decide) hm hn i₀
      have hu := (generic_middle_slHilbert_bounds (K := K) (n := n) (m := m)
        i₀ (by omega) (by omega) 7).2
      rw [generic_mixed_one_three_glHilbert 1 (by decide) hm hn] at hu
      norm_num at hl hu ⊢
      omega
    · rw [← slHilbert_eq_matrix_kernel _ _ i₀]
      rw [generic_middle_slHilbert_high i₀ (by omega) (by omega) 9 (by rw [hm,hn]; decide),
        generic_mixed_one_three_glHilbert 1 (by decide) hm hn]
    · intro d
      rw [← slHilbert_eq_matrix_kernel _ _ i₀]
      have hu := (generic_middle_slHilbert_bounds (K := K) (n := n) (m := m)
        i₀ (by omega) (by omega) d).2
      rw [generic_mixed_one_three_glHilbert 1 (by decide) hm hn] at hu
      have h0 := Nat.mul_le_mul_left 3 (Nat.sub_le (d+1) 7)
      have h1 := Nat.mul_le_mul_left 9 (Nat.sub_le (d+1) 8)
      norm_num only [Nat.reduceAdd,Nat.reduceMul] at hu ⊢
      omega
  exact hasMinimalKernelDegrees_balanced_of_adjacent _ 12 1 7 (by decide) hprofile

end FD56
