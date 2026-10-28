/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.ResidueOneScalarLifts

/-! Uniform scalar-lift frames for all state counts mq+1. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2048
variable (m : ℕ) [NeZero m]

def residueOneFrameDegree (q : ℕ) : ℕ := (m*q^2+(m+2)*q)/2

theorem residueOne_prefix_row_weight (q : ℕ) :
    2*(∑ k : Fin (m*q), (k.val/m+1))=m*q*(q+1) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ,Fin.sum_univ_add]
    simp only [Fin.coe_castAdd,Fin.coe_natAdd]
    have h (i : Fin m) : (m*q+i.val)/m=q := by
      rw [Nat.mul_add_div (NeZero.pos m),Nat.div_eq_of_lt i.isLt,Nat.add_zero]
    simp_rw [h]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
    nlinarith

theorem residueOne_row_weight (q : ℕ) :
    (∑ k : Fin (m*q+1), (residueOneLevel m q k+1))=residueOneFrameDegree m q+1 := by
  have hs : 2*(∑ k : Fin (m*q+1), (residueOneLevel m q k+1))=m*q^2+(m+2)*q+2 := by
    simp only [residueOneLevel,Fin.sum_univ_castSucc,Fin.coe_castSucc,Fin.val_last]
    rw [Nat.mul_div_cancel_left q (NeZero.pos m)]
    nlinarith [residueOne_prefix_row_weight m q]
  unfold residueOneFrameDegree
  omega

variable {R : Type*} [CommRing R]

theorem residueOne_prefix_zero_count (q : ℕ) :
    (∑ k : Fin (m*q), if k.val%m=0 then (1 : R) else 0)=(q : R) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ,Fin.sum_univ_add]
    simp only [Fin.coe_castAdd,Fin.coe_natAdd]
    rw [ih]
    have h (i : Fin m) : (m*q+i.val)%m=0 ↔ i=0 := by
      have he : (m*q+i.val)%m=i.val := by simp [Nat.add_mod,Nat.mod_eq_of_lt i.isLt]
      rw [he]
      constructor
      · intro hi; exact Fin.ext (by simpa using hi)
      · intro hi; simp [hi]
    simp_rw [h]
    simp

theorem residueOne_shift_scalarU_zero (q : ℕ) :
    residueOneScalarLiftMatrix m q (residueOneShiftM (R:=R) m q) (residueOneShiftP m q) (.inr (0,0)) 0=
      (q+1 : ℕ) := by
  have hsum : (∑ k : Fin (m*q+1), if k.val%m=0 then (1 : R) else 0)=((q+1 : ℕ) : R) := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc,Fin.val_last]
    rw [residueOne_prefix_zero_count m q]
    simp
  change observabilityScalarU (residueOneShiftM (R:=R) m q)
    (observabilitySelectedMatrix (residueOneShiftM m q) (residueOneShiftP m q)
      (residueOneLevel m q) (residueOneRow m q 0)).adjugate
      (residueOneLevel m q) (residueOneRow m q 0) 0 0=_
  rw [residueOne_shift_selected_zero,Matrix.adjugate_one]
  rw [← hsum]
  simp only [observabilityScalarU,Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  have hk := Nat.mod_add_div k.val m
  have hmq : m*q/m=q := Nat.mul_div_cancel_left q (NeZero.pos m)
  simp [Matrix.mul_apply,observabilityScalarColumn,Matrix.one_apply,
    residueOneShiftM,finiteShiftMatrix_pow,finiteShiftMatrix,residueOneLevel,residueOneRow]
  split_ifs <;> simp_all <;> omega

variable {K : Type*} [Field K]

theorem residueOne_scalar_lift_degree (q : ℕ)
    (M : Matrix (Fin (m*q+1)) (Fin (m*q+1)) K[X])
    (P : Matrix (Fin m) (Fin (m*q+1)) K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) :
    DegreeBound (residueOneScalarLiftMatrix m q M P) (residueOneFrameDegree m q) := by
  intro k j
  obtain ⟨hX,hU,_⟩ := observability_adjugate_solution_degree M P hM hP
    (residueOneLevel m q) (residueOneRow m q j) (residueOneFrameDegree m q) (residueOne_row_weight m q)
  rcases k with ab|ab
  · exact hX ab.1 ab.2
  · exact hU ab.1 ab.2

theorem residueOne_shift_scalar_lift_injective [CharZero K] (q : ℕ) :
    Function.Injective (residueOneScalarLiftMatrix m q
      (residueOneShiftM (R:=K) m q) (residueOneShiftP m q)).mulVec := by
  change Function.Injective (Matrix.toLin' (residueOneScalarLiftMatrix m q
    (residueOneShiftM (R:=K) m q) (residueOneShiftP m q)))
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  change residueOneScalarLiftMatrix m q (residueOneShiftM (R:=K) m q) (residueOneShiftP m q)*ᵥv=0 at hv
  have hentry (a b : Fin m) (ha : a≠0) :
      residueOneScalarLiftMatrix m q (residueOneShiftM (R:=K) m q) (residueOneShiftP m q) (.inr (0,b)) a=
        if b=a then 1 else 0 := residueOne_shift_scalarU m q a b ha
  have h0 := congrFun hv (.inr (0,0))
  have hv0 : v 0=0 := by
    have hsum : (∑ a : Fin m, residueOneScalarLiftMatrix m q (residueOneShiftM (R:=K) m q)
        (residueOneShiftP m q) (.inr (0,0)) a*v a)=((q+1 : ℕ) : K)*v 0 := by
      rw [Finset.sum_eq_single 0]
      · rw [residueOne_shift_scalarU_zero]
      · intro a _ ha
        rw [hentry a 0 ha,if_neg (Ne.symm ha),zero_mul]
      · simp
    change (∑ a : Fin m, residueOneScalarLiftMatrix m q (residueOneShiftM (R:=K) m q)
        (residueOneShiftP m q) (.inr (0,0)) a*v a)=0 at h0
    rw [hsum] at h0
    exact (mul_eq_zero.mp h0).resolve_left (by exact_mod_cast (Nat.succ_ne_zero q))
  funext b
  by_cases hb : b=0
  · simpa [hb] using hv0
  have he := congrFun hv (.inr (0,b))
  change (∑ a : Fin m, residueOneScalarLiftMatrix m q (residueOneShiftM (R:=K) m q)
      (residueOneShiftP m q) (.inr (0,b)) a*v a)=0 at he
  rw [Finset.sum_eq_single b] at he
  · simpa [hentry b b hb] using he
  · intro a _ ha
    by_cases ha0 : a=0
    · simp [ha0,hv0]
    · rw [hentry a b ha0,if_neg (Ne.symm ha),zero_mul]
  · simp

end FD56
