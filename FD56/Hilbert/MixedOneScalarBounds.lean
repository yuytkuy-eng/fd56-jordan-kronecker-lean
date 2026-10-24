/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MixedSLCriticalBound

/-! Dimension lower bounds for quotient one with arbitrary positive numbers of high-degree columns. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem generic_mixed_one_slHilbert_dimension_lower
    (u v d : ℕ) (hu : 0<u) (hv : 0<v) (hd : 3≤d)
    (hm : Fintype.card m=u+2*v) (hn : Fintype.card n=2*u+3*v) (i₀ : n) :
    ((u+v)*v+1)*d+2-(3*u^2+8*u*v+6*v^2) ≤
      slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) d := by
  letI : Nonempty n := ⟨i₀⟩
  have hmn : Fintype.card m < Fintype.card n := by omega
  obtain ⟨B,hB,hBL⟩ := generic_mixed_kernel_basis (K := K) (n := n) (m := m)
    1 u v hu (by omega) (by omega)
  obtain ⟨R,_,hPR⟩ := generic_affine_rows_right_inverse_of_sizes K m n (by omega) hmn
  have hPL := matrix_transpose_injective_of_surjective _
    (generic_affine_rows_leading_surjective K m n hmn.le)
  have hh := weighted_middle_slHilbert_lower _ _ B R hPR
    (mixedKernelDegree 1 u v) (Sum.elim (fun _ => d-2) (fun _ => d-3)) d
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
  have he : (u*(Fintype.card m*(d-2+1))+v*(Fintype.card m*(d-3+1))+(d+2))+
      (3*u^2+8*u*v+6*v^2) =
      (u*(u*(d-2+4)+v*(d-2+5))+v*(u*(d-3+4)+v*(d-3+5)))+((u+v)*v+1)*d+2 := by
    rw [hm]
    nlinarith only [congrArg (fun x => u*(u+2*v)*x) h2,
      congrArg (fun x => v*(u+2*v)*x) h3,
      congrArg (fun x => u*u*x) h2,congrArg (fun x => v*u*x) h2,
      congrArg (fun x => v*u*x) h3,congrArg (fun x => v*v*x) h3]
  omega

end FD56
