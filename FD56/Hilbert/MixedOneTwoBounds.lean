/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MixedSLCriticalBound

/-! Sharp dimension lower bounds for quotient one with two high-degree columns. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem generic_mixed_one_two_slHilbert_lower
    (u d : ℕ) (hu : 0 < u) (hd : 3 ≤ d)
    (hm : Fintype.card m=u+4) (hn : Fintype.card n=2*u+6) (i₀ : n) :
    (2*u+5)*d-(3*u^2+16*u+22) ≤
      slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) d := by
  letI : Nonempty n := ⟨i₀⟩
  have hmn : Fintype.card m < Fintype.card n := by omega
  obtain ⟨B,hB,hBL⟩ := generic_mixed_kernel_basis (K := K) (n := n) (m := m)
    1 u 2 hu (by omega) (by omega)
  obtain ⟨R,_,hPR⟩ := generic_affine_rows_right_inverse_of_sizes K m n (by omega) hmn
  have hPL := matrix_transpose_injective_of_surjective _
    (generic_affine_rows_leading_surjective K m n hmn.le)
  have hh := weighted_middle_slHilbert_lower _ _ B R hPR
    (mixedKernelDegree 1 u 2) (Sum.elim (fun _ => d-2) (fun _ => d-3)) d
    (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m) hB hBL hPL
    (by intro i; cases i <;> simp only [mixedKernelDegree_inl,mixedKernelDegree_inr,
      Sum.elim_inl,Sum.elim_inr] <;> omega)
    (by intro i; cases i <;> simp only [mixedKernelDegree_inl,mixedKernelDegree_inr,
      Sum.elim_inl,Sum.elim_inr] <;> omega) (Sum.inl ⟨0,hu⟩)
  simp only [Fintype.sum_sum_type,mixedKernelDegree_inl,mixedKernelDegree_inr,
    Sum.elim_inl,Sum.elim_inr,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    smul_eq_mul,one_mul,Nat.add_assoc] at hh
  norm_num only [Nat.reduceAdd] at hh
  have h2 : d-2+2=d := Nat.sub_add_cancel (by omega)
  have h3 : d-3+3=d := Nat.sub_add_cancel hd
  have he : (u*(Fintype.card m*(d-2+1))+2*(Fintype.card m*(d-3+1))+(d+2))+
      (3*u^2+16*u+22) =
      (u*(u*(d-2+4)+2*(d-2+5))+2*(u*(d-3+4)+2*(d-3+5)))+(2*u+5)*d := by
    rw [hm]
    nlinarith only [congrArg (fun x => u*(u+4)*x) h2,
      congrArg (fun x => 2*(u+4)*x) h3,
      congrArg (fun x => u*u*x) h2,congrArg (fun x => 2*u*x) h2,
      congrArg (fun x => 2*u*x) h3,congrArg (fun x => 4*x) h3]
  omega

theorem generic_mixed_one_two_even_slHilbert_lower (k : ℕ) (hk : 0 < k)
    (hm : Fintype.card m=2*k+4) (hn : Fintype.card n=4*k+6) (i₀ : n) :
    3*k+3 ≤ slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) (3*k+5) := by
  have hh := generic_mixed_one_two_slHilbert_lower (K := K) (2*k) (3*k+5)
    (by omega) (by omega) hm (by omega) i₀
  have he : (2*(2*k)+5)*(3*k+5) = (3*(2*k)^2+16*(2*k)+22)+(3*k+3) := by ring
  rw [he,Nat.add_sub_cancel_left] at hh
  exact hh

theorem generic_mixed_one_two_odd_slHilbert_lower (k : ℕ)
    (hm : Fintype.card m=2*k+5) (hn : Fintype.card n=4*k+8) (i₀ : n) :
    k+1 ≤ slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) (3*k+6) := by
  have hh := generic_mixed_one_two_slHilbert_lower (K := K) (n := n) (m := m) (2*k+1) (3*k+6)
    (by omega) (by omega) (by omega) (by omega) i₀
  have he : (2*(2*k+1)+5)*(3*k+6) = (3*(2*k+1)^2+16*(2*k+1)+22)+(k+1) := by ring
  rw [he,Nat.add_sub_cancel_left] at hh
  exact hh

end FD56
