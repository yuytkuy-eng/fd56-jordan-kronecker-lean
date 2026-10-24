/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MixedOneScalarBounds
import FD56.Hilbert.GenericMiddleSLHigh

/-! General lower bounds and an infinite obstruction to balanced SL degrees
in the quotient-one range. These bounds do not assert scalar maximal rank. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem generic_mixed_one_slHilbert_lower_envelope
    (u v d : ℕ) (hu : 0 < u) (hv : 0 < v) (hd : 3 ≤ d)
    (hm : Fintype.card m = u+2*v) (hn : Fintype.card n = 2*u+3*v) (i₀ : n) :
    max
      (Module.finrank (AffineCoefficientField K (MatrixParameters n m))
        (polynomialKernelAtDegree (glEquationMatrix
          (genericAffineSquare K n m) (genericAffineRows K n m)) d))
      (((u+v)*v+1)*d+2-(3*u^2+8*u*v+6*v^2)) ≤
        slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) d := by
  exact max_le
    (generic_middle_slHilbert_bounds i₀ (by omega) (by omega) d).1
    (generic_mixed_one_slHilbert_dimension_lower u v d hu hv hd hm hn i₀)

theorem generic_mixed_one_first_low_glHilbert_six
    (v : ℕ) (hv : 4 ≤ v)
    (hm : Fintype.card m = 2*v+1) (hn : Fintype.card n = 3*v+2) :
    Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (polynomialKernelAtDegree (glEquationMatrix
        (genericAffineSquare K n m) (genericAffineRows K n m)) 6) = v-3 := by
  have hG := (hasMinimalKernelDegrees_iff_hilbert _ _).mp
    (generic_middle_gl_minimal_degrees (K := K) (n := n) (m := m)
      (by omega) (by omega)) 6
  have hr : Fintype.card n-Fintype.card m = v+1 := by omega
  have hs : Fintype.card m-(Fintype.card n-Fintype.card m) = v := by omega
  have ha : (2*v+1)/(v+1)=1 := by apply Nat.div_eq_of_lt_le <;> omega
  have ham : (2*v+1)%(v+1)=v := by rw [Nat.mod_eq_sub_mul_div, ha]; omega
  have hb : (2*v+1+2*(v+1))/v=4 := by apply Nat.div_eq_of_lt_le <;> omega
  have hbm : (2*v+1+2*(v+1))%v=3 := by rw [Nat.mod_eq_sub_mul_div,hb]; omega
  rw [hs,hr,hm] at hG
  rw [hG]
  simp only [balancedDegreeList,ha,ham,hb,hbm,show v+1-v=1 by omega,
    degreeConvolution,List.map_flatMap,nat_sum_flatMap,List.map_append,List.map_replicate,
    List.map_map,List.sum_append,List.sum_replicate,smul_eq_mul,Function.comp_apply]
  simp

theorem generic_mixed_one_first_low_sl_not_balanced
    (v : ℕ) (hv : 4 ≤ v)
    (hm : Fintype.card m = 2*v+1) (hn : Fintype.card n = 3*v+2) (i₀ : n) :
    ¬ HasMinimalKernelDegrees (slEquationMatrix (genericAffineSquare K n m)
      (genericAffineRows K n m) i₀)
      (balancedDegreeList (7*v^2+9*v+2) (v^2+v+1)) := by
  intro h
  have hh := (hasMinimalKernelDegrees_iff_hilbert _ _).mp h 6
  rw [← slHilbert_eq_matrix_kernel _ _ i₀,
    balancedDegreeList_hilbert _ _ _ (by omega)] at hh
  have hg := (generic_middle_slHilbert_bounds (K := K) (n := n) (m := m)
    i₀ (by omega) (by omega) 6).1
  rw [generic_mixed_one_first_low_glHilbert_six v hv hm hn,hh] at hg
  have he : (v^2+v+1)*(6+1) ≤ 7*v^2+9*v+2 := by nlinarith
  rw [Nat.sub_eq_zero_of_le he] at hg
  omega

end FD56
