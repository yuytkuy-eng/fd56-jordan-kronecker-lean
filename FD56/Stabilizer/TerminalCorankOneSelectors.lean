/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.ObservabilityScalarAdjugate
import FD56.LinearAlgebra.FiniteShiftMatrix

/-! Lower-closed terminal selections for m outputs and state count mq+m-1. -/

namespace FD56
open Matrix
open scoped BigOperators
variable (s : ℕ)

def terminalOneLevel (q : ℕ) (k : Fin ((s+2)*q+s+1)) : ℕ := k.val/(s+2)
def terminalOneRow (q : ℕ) (j : Fin (s+2)) (k : Fin ((s+2)*q+s+1)) : Fin (s+2) :=
  if j≠0 ∧ k.val=(s+2)*q+(j.val-1) then Fin.last (s+1)
  else ⟨k.val%(s+2),Nat.mod_lt _ (by omega)⟩
def terminalOneMissing (q : ℕ) (a : Fin (s+1)) : Fin ((s+2)*q+s+1) :=
  ⟨(s+2)*q+a.val,by omega⟩

theorem terminalOne_lower_closed (q : ℕ) (j : Fin (s+2)) :
    ∀ k t, t<terminalOneLevel s q k → ∀ a, ∃ l,
      terminalOneLevel s q l=t ∧ terminalOneRow s q j l=a := by
  intro k t ht a
  have hk : k.val/(s+2)≤q :=
    (Nat.div_le_iff_le_mul_add_pred (by omega : 0<s+2)).mpr (by omega)
  have ht' : t<q := by dsimp [terminalOneLevel] at ht; omega
  let l : Fin ((s+2)*q+s+1) := ⟨(s+2)*t+a.val,by nlinarith [a.isLt]⟩
  refine ⟨l,?_,?_⟩
  · dsimp [terminalOneLevel,l]
    rw [Nat.mul_add_div (by omega : 0<s+2),Nat.div_eq_of_lt a.isLt,Nat.add_zero]
  · have hne : ¬(j≠0 ∧ l.val=(s+2)*q+(j.val-1)) := by
      intro h
      have he := h.2
      dsimp [l] at he
      nlinarith [a.isLt]
    simp only [terminalOneRow,hne,↓reduceIte]
    apply Fin.ext
    simp [l,Nat.add_mod,Nat.mod_eq_of_lt a.isLt]

@[simp] theorem terminalOneLevel_missing (q : ℕ) (a : Fin (s+1)) :
    terminalOneLevel s q (terminalOneMissing s q a)=q := by
  dsimp [terminalOneLevel,terminalOneMissing]
  rw [Nat.mul_add_div (by omega : 0<s+2),Nat.div_eq_of_lt (by omega : a.val<s+2),Nat.add_zero]

@[simp] theorem terminalOneRow_missing (q : ℕ) (a : Fin (s+1)) :
    terminalOneRow s q a.succ (terminalOneMissing s q a)=Fin.last (s+1) := by
  simp [terminalOneRow,terminalOneMissing]

variable {R : Type*} [CommRing R]
def terminalOneShiftM (q : ℕ) : Matrix (Fin ((s+2)*q+s+1)) (Fin ((s+2)*q+s+1)) R :=
  finiteShiftMatrix ((s+2)*q+s+1) (s+2)
def terminalOneShiftP (q : ℕ) : Matrix (Fin (s+2)) (Fin ((s+2)*q+s+1)) R :=
  finiteInitialRows (s+2) ((s+2)*q+s+1)

theorem terminalOne_shift_selected_zero (q : ℕ) :
    observabilitySelectedMatrix (terminalOneShiftM (R:=R) s q) (terminalOneShiftP s q)
      (terminalOneLevel s q) (terminalOneRow s q 0)=1 := by
  ext i j
  simp only [observabilitySelectedMatrix,terminalOneShiftM,terminalOneShiftP,
    finiteShiftMatrix_pow,finiteInitialRows_mul_shift]
  rw [finiteInitialRows_mul_shift]
  dsimp only
  have hi : (terminalOneRow s q 0 i).val+(s+2)*terminalOneLevel s q i=i.val := by
    simp only [terminalOneRow,ne_eq,not_true_eq_false,false_and,↓reduceIte,terminalOneLevel]
    exact Nat.mod_add_div _ _
  rw [hi]
  simp [Matrix.one_apply,Fin.ext_iff]

theorem terminalOne_shift_selected_succ (q : ℕ) (a : Fin (s+1)) :
    observabilitySelectedMatrix (terminalOneShiftM (R:=R) s q) (terminalOneShiftP s q)
      (terminalOneLevel s q) (terminalOneRow s q a.succ)=
      Matrix.diagonal (fun i : Fin ((s+2)*q+s+1) =>
        if i=terminalOneMissing s q a then (0 : R) else 1) := by
  ext i j
  simp only [observabilitySelectedMatrix,terminalOneShiftM,terminalOneShiftP,
    finiteShiftMatrix_pow,finiteInitialRows_mul_shift]
  rw [finiteInitialRows_mul_shift]
  dsimp only
  by_cases hi : i=terminalOneMissing s q a
  · subst i
    have hj : s+1+(s+2)*q≠j.val := by omega
    simp [terminalOneLevel_missing,terminalOneRow_missing,Matrix.diagonal_apply,hj]
  · have hval : i.val≠(s+2)*q+a.val := fun h => hi (Fin.ext h)
    have he : (terminalOneRow s q a.succ i).val+(s+2)*terminalOneLevel s q i=i.val := by
      simp only [terminalOneRow,Fin.succ_ne_zero,ne_eq,not_false_eq_true,Fin.val_succ,
        Nat.add_sub_cancel,true_and,hval,↓reduceIte,terminalOneLevel]
      exact Nat.mod_add_div _ _
    rw [he]
    simp [Matrix.diagonal_apply,hi,Fin.ext_iff,terminalOneMissing,hval]

theorem terminalOne_shift_selected_adjugate (q : ℕ) (a : Fin (s+1)) :
    (observabilitySelectedMatrix (terminalOneShiftM (R:=R) s q) (terminalOneShiftP s q)
      (terminalOneLevel s q) (terminalOneRow s q a.succ)).adjugate=
      Matrix.diagonal (fun i : Fin ((s+2)*q+s+1) =>
        if i=terminalOneMissing s q a then (1 : R) else 0) := by
  rw [terminalOne_shift_selected_succ,Matrix.adjugate_diagonal]
  apply congrArg Matrix.diagonal
  funext i
  by_cases hi : i=terminalOneMissing s q a
  · subst i; simp
  · rw [if_neg hi]
    apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hi,Finset.mem_univ _⟩)
    simp

theorem terminalOne_shift_scalarU (q : ℕ) (a : Fin (s+1))
    (i : Fin ((s+2)*q+s+1)) (b : Fin (s+2)) :
    observabilityScalarU (terminalOneShiftM (R:=R) s q)
      (observabilitySelectedMatrix (terminalOneShiftM s q) (terminalOneShiftP s q)
        (terminalOneLevel s q) (terminalOneRow s q a.succ)).adjugate
      (terminalOneLevel s q) (terminalOneRow s q a.succ) i b=
        if i.val=a.val ∧ b=Fin.last (s+1) then 1 else 0 := by
  rw [terminalOne_shift_selected_adjugate]
  simp only [observabilityScalarU,Matrix.sum_apply,Matrix.mul_apply,
    observabilityScalarColumn,Matrix.diagonal_apply]
  rw [Finset.sum_eq_single (terminalOneMissing s q a)]
  · simp [terminalOneShiftM,finiteShiftMatrix_pow,finiteShiftMatrix,ite_mul,
      terminalOneMissing,terminalOneLevel,terminalOneRow,
      Nat.mul_add_div (by omega : 0<s+2),Nat.div_eq_of_lt (by omega : a.val<s+2)]
    split_ifs <;> simp_all <;> omega
  · intro k _ hk
    apply Finset.sum_eq_zero
    intro l _
    by_cases hl : l=k
    · subst l; simp [hk]
    · simp [hl]
  · simp

end FD56
