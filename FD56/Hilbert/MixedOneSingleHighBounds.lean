/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MixedSLCriticalBound

/-! Dimension bounds for quotient one with a single high-degree column. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

private theorem list_hilbert_le_length (es : List ℕ) (d : ℕ) :
    (es.map (fun e => d+1-e)).sum ≤ es.length*(d+1) := by
  induction es with
  | nil => simp
  | cons e es ih =>
    simpa only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,one_mul,
      Nat.add_comm] using Nat.add_le_add (Nat.sub_le (d+1) e) ih

private theorem degreeConvolution_length (alpha beta : List ℕ) :
    (degreeConvolution alpha beta).length = alpha.length*beta.length := by
  induction alpha with
  | nil => simp [degreeConvolution]
  | cons a alpha ih =>
    simp only [degreeConvolution,List.flatMap_cons,List.length_append,List.length_map,
      List.length_cons,Nat.add_mul,one_mul] at ih ⊢
    omega

variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem generic_mixed_one_single_high_slHilbert_lower (u : ℕ) (hu : 0 < u)
    (hm : Fintype.card m = u+2) (hn : Fintype.card n = 2*u+3) (i₀ : n) :
    u+2 ≤ slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) (3*u+3) := by
  letI : Nonempty n := ⟨i₀⟩
  have hmn : Fintype.card m < Fintype.card n := by omega
  obtain ⟨B,hB,hBL⟩ := generic_mixed_kernel_basis (K := K) (n := n) (m := m) 1 u 1 hu
    (by omega) (by omega)
  obtain ⟨R,_,hPR⟩ := generic_affine_rows_right_inverse_of_sizes K m n (by omega) hmn
  have hPL := matrix_transpose_injective_of_surjective _
    (generic_affine_rows_leading_surjective K m n hmn.le)
  have hh := weighted_middle_slHilbert_lower _ _ B R hPR
    (mixedKernelDegree 1 u 1) (Sum.elim (fun _ => 3*u+1) (fun _ => 3*u)) (3*u+3)
    (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m) hB hBL hPL
    (by intro i; cases i <;> simp only [mixedKernelDegree_inl,mixedKernelDegree_inr,
      Sum.elim_inl,Sum.elim_inr] <;> omega)
    (by intro i; cases i <;> simp only [mixedKernelDegree_inl,mixedKernelDegree_inr,
      Sum.elim_inl,Sum.elim_inr] <;> omega) (Sum.inl ⟨0,hu⟩)
  simp only [Fintype.sum_sum_type,mixedKernelDegree_inl,mixedKernelDegree_inr,
    Sum.elim_inl,Sum.elim_inr,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    smul_eq_mul,one_mul,Nat.add_assoc] at hh
  norm_num only [Nat.reduceAdd] at hh
  have he : u*(Fintype.card m*(3*u+2))+Fintype.card m*(3*u+1)+(3*u+5) =
      (u*(u*(3*u+5)+(3*u+6))+(u*(3*u+4)+(3*u+5)))+(u+2) := by rw [hm]; ring
  omega

theorem generic_mixed_one_single_high_slHilbert_upper (u : ℕ) (hu : 0 < u)
    (hm : Fintype.card m = u+2) (hn : Fintype.card n = 2*u+3) (i₀ : n) (d : ℕ) :
    slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) d ≤
      (u+2)*(d+1)+1 := by
  have hmn : Fintype.card m < Fintype.card n := by omega
  have hnm : Fintype.card n < 2*Fintype.card m := by omega
  have hr : Fintype.card n-Fintype.card m = u+1 := by omega
  have hs : Fintype.card m-(Fintype.card n-Fintype.card m) = 1 := by omega
  have hg := (hasMinimalKernelDegrees_iff_hilbert _ _).mp
    (generic_middle_gl_minimal_degrees (K := K) hmn hnm) d
  have hl := list_hilbert_le_length
    (degreeConvolution
      (balancedDegreeList (Fintype.card m) (Fintype.card n-Fintype.card m))
      (balancedDegreeList (Fintype.card m+2*(Fintype.card n-Fintype.card m))
        (Fintype.card m-(Fintype.card n-Fintype.card m)))) d
  rw [← hg,degreeConvolution_length,balancedDegreeList_length _ _ (by omega),
    balancedDegreeList_length _ _ (by omega),hs,hr,mul_one] at hl
  have hh := (generic_middle_slHilbert_bounds (K := K) i₀ hmn hnm d).2
  nlinarith

end FD56
