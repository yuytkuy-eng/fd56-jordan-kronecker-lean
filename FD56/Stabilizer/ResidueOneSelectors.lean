/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.ObservabilityScalarAdjugate
import FD56.LinearAlgebra.FiniteShiftMatrix

/-! Lower-closed terminal selections for any positive output count and state count mq+1. -/

namespace FD56
open Matrix
open scoped BigOperators
variable (m : ℕ) [NeZero m]

def residueOneLevel (q : ℕ) (k : Fin (m*q+1)) : ℕ := k.val/m
def residueOneRow (q : ℕ) (j : Fin m) (k : Fin (m*q+1)) : Fin m :=
  if k.val=m*q then j else ⟨k.val%m,Nat.mod_lt _ (NeZero.pos m)⟩

theorem residueOne_lower_closed (q : ℕ) (j : Fin m) :
    ∀ k s, s<residueOneLevel m q k → ∀ a, ∃ l,
      residueOneLevel m q l=s ∧ residueOneRow m q j l=a := by
  intro k s hs a
  have hm : 0<m := NeZero.pos m
  have hk : k.val/m≤q := (Nat.div_le_iff_le_mul_add_pred hm).mpr (by nlinarith [k.isLt])
  have hs' : s<q := by dsimp [residueOneLevel,NeZero.ne m] at hs; omega
  let l : Fin (m*q+1) := ⟨m*s+a.val,by nlinarith [a.isLt]⟩
  refine ⟨l,?_,?_⟩
  · dsimp [residueOneLevel,l]
    rw [Nat.mul_add_div hm,Nat.div_eq_of_lt a.isLt,Nat.add_zero]
  · have hne : l.val≠m*q := by dsimp [l]; nlinarith [a.isLt]
    simp only [residueOneRow,hne,↓reduceIte]
    apply Fin.ext
    simp [l,Nat.add_mod,Nat.mod_eq_of_lt a.isLt]

@[simp] theorem residueOneLevel_last (q : ℕ) : residueOneLevel m q (Fin.last (m*q))=q := by
  simp [residueOneLevel,NeZero.ne m]
@[simp] theorem residueOneRow_last (q : ℕ) (j : Fin m) :
    residueOneRow m q j (Fin.last (m*q))=j := by simp [residueOneRow]

variable {R : Type*} [CommRing R]
def residueOneShiftM (q : ℕ) : Matrix (Fin (m*q+1)) (Fin (m*q+1)) R :=
  finiteShiftMatrix (m*q+1) m
def residueOneShiftP (q : ℕ) : Matrix (Fin m) (Fin (m*q+1)) R :=
  finiteInitialRows m (m*q+1)

theorem residueOne_shift_selected_zero (q : ℕ) :
    observabilitySelectedMatrix (residueOneShiftM (R:=R) m q) (residueOneShiftP m q)
      (residueOneLevel m q) (residueOneRow m q 0)=1 := by
  ext i j
  simp only [observabilitySelectedMatrix,residueOneShiftM,residueOneShiftP,
    finiteShiftMatrix_pow,finiteInitialRows_mul_shift]
  rw [finiteInitialRows_mul_shift]
  dsimp only
  have hi : (residueOneRow m q 0 i).val+m*residueOneLevel m q i=i.val := by
    by_cases h : i.val=m*q
    · simp [residueOneRow,residueOneLevel,h,NeZero.ne m]
    · simp only [residueOneRow,h,↓reduceIte,residueOneLevel]; exact Nat.mod_add_div _ _
  rw [hi]
  simp [Matrix.one_apply,Fin.ext_iff]

theorem residueOne_shift_selected_ne_zero (q : ℕ) (a : Fin m) (ha : a≠0) :
    observabilitySelectedMatrix (residueOneShiftM (R:=R) m q) (residueOneShiftP m q)
      (residueOneLevel m q) (residueOneRow m q a)=
      Matrix.diagonal (fun i : Fin (m*q+1) => if i=Fin.last (m*q) then (0 : R) else 1) := by
  ext i j
  simp only [observabilitySelectedMatrix,residueOneShiftM,residueOneShiftP,
    finiteShiftMatrix_pow,finiteInitialRows_mul_shift]
  rw [finiteInitialRows_mul_shift]
  dsimp only
  have hap : 0<a.val := by
    have hh : a.val≠0 := fun he => ha (Fin.ext he)
    omega
  by_cases h : i.val=m*q
  · have hi : i=Fin.last (m*q) := Fin.ext h
    have hj : a.val+m*q≠j.val := by omega
    simp [residueOneRow,residueOneLevel,h,hi,Matrix.diagonal_apply,hj,NeZero.ne m]
  · have hi : i≠Fin.last (m*q) := by intro he; exact h (congrArg Fin.val he)
    have he : (residueOneRow m q a i).val+m*residueOneLevel m q i=i.val := by
      simp only [residueOneRow,h,↓reduceIte,residueOneLevel]; exact Nat.mod_add_div _ _
    rw [he]
    simp [Matrix.diagonal_apply,hi,Fin.ext_iff,h]

theorem residueOne_shift_selected_adjugate (q : ℕ) (a : Fin m) (ha : a≠0) :
    (observabilitySelectedMatrix (residueOneShiftM (R:=R) m q) (residueOneShiftP m q)
      (residueOneLevel m q) (residueOneRow m q a)).adjugate=
      Matrix.diagonal (fun i : Fin (m*q+1) => if i=Fin.last (m*q) then (1 : R) else 0) := by
  rw [residueOne_shift_selected_ne_zero m q a ha,Matrix.adjugate_diagonal]
  apply congrArg Matrix.diagonal
  funext i
  by_cases hi : i=Fin.last (m*q)
  · subst i; simp
  · rw [if_neg hi]
    apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hi,Finset.mem_univ _⟩)
    simp

theorem residueOne_shift_scalarU (q : ℕ) (a b : Fin m) (ha : a≠0) :
    observabilityScalarU (residueOneShiftM (R:=R) m q)
      (observabilitySelectedMatrix (residueOneShiftM m q) (residueOneShiftP m q)
        (residueOneLevel m q) (residueOneRow m q a)).adjugate
      (residueOneLevel m q) (residueOneRow m q a) 0 b=if b=a then 1 else 0 := by
  rw [residueOne_shift_selected_adjugate m q a ha]
  simp only [observabilityScalarU,Matrix.sum_apply,Matrix.mul_apply,
    observabilityScalarColumn,Matrix.diagonal_apply]
  rw [Finset.sum_eq_single (Fin.last (m*q))]
  · simp [residueOneShiftM,finiteShiftMatrix_pow,finiteShiftMatrix,ite_mul]
  · intro k _ hk
    apply Finset.sum_eq_zero
    intro l _
    by_cases hl : l=k
    · subst l; simp [hk]
    · simp [hl]
  · simp

end FD56
