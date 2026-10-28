/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.ObservabilityScalarAdjugate
import FD56.LinearAlgebra.FiniteShiftMatrix

/-! Lower-closed terminal selections for three outputs and state count 3q+2. -/

namespace FD56
open Matrix
open scoped BigOperators

def threeTwoLevel (q : ℕ) (k : Fin (3*q+2)) : ℕ := k.val/3
def threeTwoRow (q : ℕ) (j : Fin 3) (k : Fin (3*q+2)) : Fin 3 :=
  if j≠0 ∧ k.val=3*q+(j.val-1) then 2 else ⟨k.val%3,Nat.mod_lt _ (by decide)⟩
def threeTwoMissing (q : ℕ) (a : Fin 2) : Fin (3*q+2) := ⟨3*q+a.val,by omega⟩

theorem threeTwo_lower_closed (q : ℕ) (j : Fin 3) :
    ∀ k s, s<threeTwoLevel q k → ∀ a, ∃ l,
      threeTwoLevel q l=s ∧ threeTwoRow q j l=a := by
  intro k s hs a
  have hs' : s<q := by dsimp [threeTwoLevel] at hs; omega
  let l : Fin (3*q+2) := ⟨3*s+a.val,by omega⟩
  refine ⟨l,?_,?_⟩
  · dsimp [threeTwoLevel,l]; omega
  · have hne : ¬(j≠0 ∧ l.val=3*q+(j.val-1)) := by dsimp [l]; omega
    simp only [threeTwoRow,hne,↓reduceIte]
    apply Fin.ext
    dsimp [l]
    omega

@[simp] theorem threeTwoLevel_missing (q : ℕ) (a : Fin 2) :
    threeTwoLevel q (threeTwoMissing q a)=q := by dsimp [threeTwoLevel,threeTwoMissing]; omega
@[simp] theorem threeTwoRow_missing (q : ℕ) (a : Fin 2) :
    threeTwoRow q a.succ (threeTwoMissing q a)=2 := by simp [threeTwoRow,threeTwoMissing]

variable {R : Type*} [CommRing R]
def threeTwoShiftM (q : ℕ) : Matrix (Fin (3*q+2)) (Fin (3*q+2)) R :=
  finiteShiftMatrix (3*q+2) 3
def threeTwoShiftP (q : ℕ) : Matrix (Fin 3) (Fin (3*q+2)) R :=
  finiteInitialRows 3 (3*q+2)

theorem threeTwo_shift_selected_zero (q : ℕ) :
    observabilitySelectedMatrix (threeTwoShiftM (R:=R) q) (threeTwoShiftP q)
      (threeTwoLevel q) (threeTwoRow q 0)=1 := by
  ext i j
  simp only [observabilitySelectedMatrix,threeTwoShiftM,threeTwoShiftP,
    finiteShiftMatrix_pow,finiteInitialRows_mul_shift]
  rw [finiteInitialRows_mul_shift]
  dsimp only
  have hi : (threeTwoRow q 0 i).val+3*threeTwoLevel q i=i.val := by
    simp only [threeTwoRow,ne_eq,not_true_eq_false,false_and,↓reduceIte,threeTwoLevel]
    omega
  rw [hi]
  simp [Matrix.one_apply,Fin.ext_iff]

theorem threeTwo_shift_selected_succ (q : ℕ) (a : Fin 2) :
    observabilitySelectedMatrix (threeTwoShiftM (R:=R) q) (threeTwoShiftP q)
      (threeTwoLevel q) (threeTwoRow q a.succ)=
      Matrix.diagonal (fun i : Fin (3*q+2) => if i=threeTwoMissing q a then (0 : R) else 1) := by
  ext i j
  simp only [observabilitySelectedMatrix,threeTwoShiftM,threeTwoShiftP,
    finiteShiftMatrix_pow,finiteInitialRows_mul_shift]
  rw [finiteInitialRows_mul_shift]
  dsimp only
  by_cases hi : i=threeTwoMissing q a
  · subst i
    have hj : 2+3*q≠j.val := by omega
    simp [threeTwoLevel_missing,threeTwoRow_missing,Matrix.diagonal_apply,hj]
  · have hval : i.val≠3*q+a.val := fun h => hi (Fin.ext h)
    have he : (threeTwoRow q a.succ i).val+3*threeTwoLevel q i=i.val := by
      simp only [threeTwoRow,Fin.succ_ne_zero,ne_eq,not_false_eq_true,Fin.val_succ,
        Nat.add_sub_cancel,true_and,hval,↓reduceIte,threeTwoLevel]
      omega
    rw [he]
    simp [Matrix.diagonal_apply,hi,Fin.ext_iff,threeTwoMissing,hval]

theorem threeTwo_shift_selected_adjugate (q : ℕ) (a : Fin 2) :
    (observabilitySelectedMatrix (threeTwoShiftM (R:=R) q) (threeTwoShiftP q)
      (threeTwoLevel q) (threeTwoRow q a.succ)).adjugate=
      Matrix.diagonal (fun i : Fin (3*q+2) => if i=threeTwoMissing q a then (1 : R) else 0) := by
  rw [threeTwo_shift_selected_succ,Matrix.adjugate_diagonal]
  apply congrArg Matrix.diagonal
  funext i
  by_cases hi : i=threeTwoMissing q a
  · subst i; simp
  · rw [if_neg hi]
    apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hi,Finset.mem_univ _⟩)
    simp

theorem threeTwo_shift_scalarU (q : ℕ) (a : Fin 2) (i : Fin (3*q+2)) (b : Fin 3) :
    observabilityScalarU (threeTwoShiftM (R:=R) q)
      (observabilitySelectedMatrix (threeTwoShiftM q) (threeTwoShiftP q)
        (threeTwoLevel q) (threeTwoRow q a.succ)).adjugate
      (threeTwoLevel q) (threeTwoRow q a.succ) i b=
        if i.val=a.val ∧ b=2 then 1 else 0 := by
  rw [threeTwo_shift_selected_adjugate]
  simp only [observabilityScalarU,Matrix.sum_apply,Matrix.mul_apply,
    observabilityScalarColumn,Matrix.diagonal_apply]
  rw [Finset.sum_eq_single (threeTwoMissing q a)]
  · simp [threeTwoShiftM,finiteShiftMatrix_pow,finiteShiftMatrix,ite_mul,
      threeTwoMissing,threeTwoLevel,threeTwoRow]
    split_ifs <;> simp_all <;> omega
  · intro k _ hk
    apply Finset.sum_eq_zero
    intro l _
    by_cases hl : l=k
    · subst l; simp [hk]
    · simp [hl]
  · simp

end FD56
