/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.AdjacentCriterion
import FD56.Hilbert.MixedOneTwoBounds

/-! Adjacent SL degree profiles for two high-degree auxiliary columns. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem generic_mixed_one_two_even_glHilbert (k : ℕ) (hk : 0 < k)
    (hm : Fintype.card m=2*k+4) (hn : Fintype.card n=4*k+6) (d : ℕ) :
    Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (polynomialKernelAtDegree (glEquationMatrix
        (genericAffineSquare K n m) (genericAffineRows K n m)) d) =
      4*k*(d+1-(3*k+6))+4*(d+1-(3*k+7)) := by
  have hG := (hasMinimalKernelDegrees_iff_hilbert _ _).mp
    (generic_middle_gl_minimal_degrees (K := K) (n := n) (m := m) (by omega) (by omega)) d
  have hr : Fintype.card n-Fintype.card m=2*k+2 := by omega
  have hs : Fintype.card m-(Fintype.card n-Fintype.card m)=2 := by omega
  have ha : (2*k+4)/(2*k+2)=1 := by apply Nat.div_eq_of_lt_le <;> omega
  have ham : (2*k+4)%(2*k+2)=2 := by rw [Nat.mod_eq_sub_mul_div,ha]; omega
  have hb : (2*k+4+2*(2*k+2))/2=3*k+4 := by omega
  have hbm : (2*k+4+2*(2*k+2))%2=0 := by omega
  rw [hs,hr,hm] at hG
  rw [hG]
  simp only [balancedDegreeList,ha,ham,hb,hbm,Nat.sub_zero,
    show 2*k+2-2=2*k by omega,List.replicate_zero,List.nil_append,Nat.reduceAdd,
    degreeConvolution,List.map_flatMap,nat_sum_flatMap,List.map_append,List.map_replicate,
    List.map_map,List.sum_append,List.sum_replicate,smul_eq_mul,Function.comp_apply,
    show 1+(3*k+4)+1=3*k+6 by omega,show 2+(3*k+4)+1=3*k+7 by omega]
  ring

theorem generic_mixed_one_two_odd_glHilbert (k : ℕ)
    (hm : Fintype.card m=2*k+5) (hn : Fintype.card n=4*k+8) (d : ℕ) :
    Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (polynomialKernelAtDegree (glEquationMatrix
        (genericAffineSquare K n m) (genericAffineRows K n m)) d) =
      (2*k+1)*(d+1-(3*k+7))+(2*k+3)*(d+1-(3*k+8))+2*(d+1-(3*k+9)) := by
  have hG := (hasMinimalKernelDegrees_iff_hilbert _ _).mp
    (generic_middle_gl_minimal_degrees (K := K) (n := n) (m := m) (by omega) (by omega)) d
  have hr : Fintype.card n-Fintype.card m=2*k+3 := by omega
  have hs : Fintype.card m-(Fintype.card n-Fintype.card m)=2 := by omega
  have ha : (2*k+5)/(2*k+3)=1 := by apply Nat.div_eq_of_lt_le <;> omega
  have ham : (2*k+5)%(2*k+3)=2 := by rw [Nat.mod_eq_sub_mul_div,ha]; omega
  have hb : (2*k+5+2*(2*k+3))/2=3*k+5 := by omega
  have hbm : (2*k+5+2*(2*k+3))%2=1 := by omega
  rw [hs,hr,hm] at hG
  rw [hG]
  simp only [balancedDegreeList,ha,ham,hb,hbm,
    show 2*k+3-2=2*k+1 by omega,Nat.reduceSub,degreeConvolution,List.map_flatMap,
    nat_sum_flatMap,List.map_append,List.map_replicate,List.map_map,List.sum_append,
    List.sum_replicate,smul_eq_mul,Function.comp_apply,
    show 1+(3*k+5)+1=3*k+7 by omega,show 2+(3*k+5)+1=3*k+8 by omega,
    show 1+(3*k+5+1)+1=3*k+8 by omega,show 2+(3*k+5+1)+1=3*k+9 by omega]
  ring

theorem generic_mixed_one_two_even_slHilbert_later (k : ℕ) (hk : 0 < k)
    (hm : Fintype.card m=2*k+4) (hn : Fintype.card n=4*k+6) (i₀ : n) :
    slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) (3*k+7) = 11*k+13 := by
  have hr : Fintype.card n-Fintype.card m=2*k+2 := by omega
  have hs : Fintype.card m-(Fintype.card n-Fintype.card m)=2 := by omega
  have ha : (2*k+4)/(2*k+2)=1 := by apply Nat.div_eq_of_lt_le <;> omega
  rw [generic_middle_slHilbert_high i₀ (by omega) (by omega) (3*k+7)
    (by rw [hs,hr,hm,ha]; omega),generic_mixed_one_two_even_glHilbert k hk hm hn]
  have h0 : 3*k+7+1-(3*k+6)=2 := by omega
  have h1 : 3*k+7+1-(3*k+7)=1 := by omega
  rw [h0,h1]
  ring

theorem generic_mixed_one_two_odd_slHilbert_later (k : ℕ)
    (hm : Fintype.card m=2*k+5) (hn : Fintype.card n=4*k+8) (i₀ : n) :
    slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) (3*k+8) = 9*k+15 := by
  have hr : Fintype.card n-Fintype.card m=2*k+3 := by omega
  have hs : Fintype.card m-(Fintype.card n-Fintype.card m)=2 := by omega
  have ha : (2*k+5)/(2*k+3)=1 := by apply Nat.div_eq_of_lt_le <;> omega
  rw [generic_middle_slHilbert_high i₀ (by omega) (by omega) (3*k+8)
    (by rw [hs,hr,hm,ha]; omega),generic_mixed_one_two_odd_glHilbert k hm hn]
  have h0 : 3*k+8+1-(3*k+7)=2 := by omega
  have h1 : 3*k+8+1-(3*k+8)=1 := by omega
  have h2 : 3*k+8+1-(3*k+9)=0 := by omega
  rw [h0,h1,h2]
  ring

theorem generic_mixed_one_two_even_sl_minimal_degrees_of_bounds (k : ℕ) (hk : 0 < k)
    (hm : Fintype.card m=2*k+4) (hn : Fintype.card n=4*k+6) (i₀ : n)
    (hzero : slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) (3*k+4)=0)
    (hupper : slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) (3*k+5) ≤ 3*k+3) :
    HasMinimalKernelDegrees (slEquationMatrix (genericAffineSquare K n m)
      (genericAffineRows K n m) i₀)
      (List.replicate (3*k+3) (3*k+5) ++ List.replicate (k+2) (3*k+6)) := by
  apply hasMinimalKernelDegrees_adjacent_of_bounds _ (3*k+5) (3*k+3) (k+2) 1 (by omega)
  · rw [← slHilbert_eq_matrix_kernel _ _ i₀]
    simpa only [show 3*k+5-1=3*k+4 by omega] using hzero
  · rw [← slHilbert_eq_matrix_kernel _ _ i₀]
    exact Nat.le_antisymm hupper (generic_mixed_one_two_even_slHilbert_lower k hk hm hn i₀)
  · rw [← slHilbert_eq_matrix_kernel _ _ i₀]
    have hh := generic_mixed_one_two_even_slHilbert_later (K := K) k hk hm hn i₀
    simpa only [Nat.add_assoc,Nat.reduceAdd] using (show 3*(3*k+3)+2*(k+2) ≤
      slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) (3*k+7) by rw [hh]; omega)
  · intro d
    rw [← slHilbert_eq_matrix_kernel _ _ i₀]
    have hh := (generic_middle_slHilbert_bounds (K := K) (n := n) (m := m) i₀ (by omega) (by omega) d).2
    rw [generic_mixed_one_two_even_glHilbert k hk hm hn] at hh
    have h0 := Nat.sub_le (d+1) (3*k+6)
    have h1 := Nat.sub_le (d+1) (3*k+7)
    have hm0 := Nat.mul_le_mul_left (4*k) h0
    have hm1 := Nat.mul_le_mul_left 4 h1
    nlinarith

theorem generic_mixed_one_two_odd_sl_minimal_degrees_of_bounds (k : ℕ)
    (hm : Fintype.card m=2*k+5) (hn : Fintype.card n=4*k+8) (i₀ : n)
    (hzero : slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) (3*k+5)=0)
    (hupper : slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) (3*k+6) ≤ k+1) :
    HasMinimalKernelDegrees (slEquationMatrix (genericAffineSquare K n m)
      (genericAffineRows K n m) i₀)
      (List.replicate (k+1) (3*k+6) ++ List.replicate (3*k+6) (3*k+7)) := by
  apply hasMinimalKernelDegrees_adjacent_of_bounds _ (3*k+6) (k+1) (3*k+6) 1 (by omega)
  · rw [← slHilbert_eq_matrix_kernel _ _ i₀]
    simpa only [show 3*k+6-1=3*k+5 by omega] using hzero
  · rw [← slHilbert_eq_matrix_kernel _ _ i₀]
    exact Nat.le_antisymm hupper (generic_mixed_one_two_odd_slHilbert_lower k hm hn i₀)
  · rw [← slHilbert_eq_matrix_kernel _ _ i₀]
    have hh := generic_mixed_one_two_odd_slHilbert_later (K := K) k hm hn i₀
    simpa only [Nat.add_assoc,Nat.reduceAdd] using (show 3*(k+1)+2*(3*k+6) ≤
      slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) (3*k+8) by rw [hh]; omega)
  · intro d
    rw [← slHilbert_eq_matrix_kernel _ _ i₀]
    have hh := (generic_middle_slHilbert_bounds (K := K) (n := n) (m := m) i₀ (by omega) (by omega) d).2
    rw [generic_mixed_one_two_odd_glHilbert k hm hn] at hh
    have h0 := Nat.mul_le_mul_left (2*k+1) (Nat.sub_le (d+1) (3*k+7))
    have h1 := Nat.mul_le_mul_left (2*k+3) (Nat.sub_le (d+1) (3*k+8))
    have h2 := Nat.mul_le_mul_left 2 (Nat.sub_le (d+1) (3*k+9))
    nlinarith

end FD56
