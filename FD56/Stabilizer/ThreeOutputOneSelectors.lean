/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.ObservabilityScalarAdjugate
import FD56.LinearAlgebra.FiniteShiftMatrix

/-! Lower-closed terminal selections for three outputs and state count 3q+1. -/

namespace FD56
open Matrix
open scoped BigOperators

def threeOneLevel (q : ℕ) (k : Fin (3*q+1)) : ℕ := k.val/3
def threeOneRow (q : ℕ) (j : Fin 3) (k : Fin (3*q+1)) : Fin 3 :=
  if k.val=3*q then j else ⟨k.val%3,Nat.mod_lt _ (by decide)⟩

theorem threeOne_lower_closed (q : ℕ) (j : Fin 3) :
    ∀ k s, s<threeOneLevel q k → ∀ a, ∃ l,
      threeOneLevel q l=s ∧ threeOneRow q j l=a := by
  intro k s hs a
  have hs' : s<q := by dsimp [threeOneLevel] at hs; omega
  let l : Fin (3*q+1) := ⟨3*s+a.val,by omega⟩
  refine ⟨l,?_,?_⟩
  · dsimp [threeOneLevel,l]; omega
  · have hne : l.val≠3*q := by dsimp [l]; omega
    simp only [threeOneRow,hne,↓reduceIte]
    apply Fin.ext
    dsimp [l]
    omega

@[simp] theorem threeOneLevel_last (q : ℕ) : threeOneLevel q (Fin.last (3*q))=q := by
  simp [threeOneLevel]
@[simp] theorem threeOneRow_last (q : ℕ) (j : Fin 3) :
    threeOneRow q j (Fin.last (3*q))=j := by simp [threeOneRow]

variable {R : Type*} [CommRing R]
def threeOneShiftM (q : ℕ) : Matrix (Fin (3*q+1)) (Fin (3*q+1)) R :=
  finiteShiftMatrix (3*q+1) 3
def threeOneShiftP (q : ℕ) : Matrix (Fin 3) (Fin (3*q+1)) R :=
  finiteInitialRows 3 (3*q+1)

theorem threeOne_shift_selected_zero (q : ℕ) :
    observabilitySelectedMatrix (threeOneShiftM (R:=R) q) (threeOneShiftP q)
      (threeOneLevel q) (threeOneRow q 0)=1 := by
  ext i j
  simp only [observabilitySelectedMatrix,threeOneShiftM,threeOneShiftP,
    finiteShiftMatrix_pow,finiteInitialRows_mul_shift]
  rw [finiteInitialRows_mul_shift]
  dsimp only
  have hi : (threeOneRow q 0 i).val+3*threeOneLevel q i=i.val := by
    by_cases h : i.val=3*q
    · simp [threeOneRow,threeOneLevel,h]
    · simp only [threeOneRow,h,↓reduceIte,threeOneLevel]; omega
  rw [hi]
  simp [Matrix.one_apply,Fin.ext_iff]

theorem threeOne_shift_selected_ne_zero (q : ℕ) (a : Fin 3) (ha : a≠0) :
    observabilitySelectedMatrix (threeOneShiftM (R:=R) q) (threeOneShiftP q)
      (threeOneLevel q) (threeOneRow q a)=
      Matrix.diagonal (fun i : Fin (3*q+1) => if i=Fin.last (3*q) then (0 : R) else 1) := by
  ext i j
  simp only [observabilitySelectedMatrix,threeOneShiftM,threeOneShiftP,
    finiteShiftMatrix_pow,finiteInitialRows_mul_shift]
  rw [finiteInitialRows_mul_shift]
  dsimp only
  have hap : 0<a.val := by
    have hh : a.val≠0 := fun he => ha (Fin.ext he)
    omega
  by_cases h : i.val=3*q
  · have hi : i=Fin.last (3*q) := Fin.ext h
    have hj : a.val+3*q≠j.val := by omega
    simp [threeOneRow,threeOneLevel,h,hi,Matrix.diagonal_apply,hj]
  · have hi : i≠Fin.last (3*q) := by intro he; exact h (congrArg Fin.val he)
    have he : (threeOneRow q a i).val+3*threeOneLevel q i=i.val := by
      simp only [threeOneRow,h,↓reduceIte,threeOneLevel]; omega
    rw [he]
    simp [Matrix.diagonal_apply,hi,Fin.ext_iff,h]

theorem threeOne_shift_selected_adjugate (q : ℕ) (a : Fin 3) (ha : a≠0) :
    (observabilitySelectedMatrix (threeOneShiftM (R:=R) q) (threeOneShiftP q)
      (threeOneLevel q) (threeOneRow q a)).adjugate=
      Matrix.diagonal (fun i : Fin (3*q+1) => if i=Fin.last (3*q) then (1 : R) else 0) := by
  rw [threeOne_shift_selected_ne_zero q a ha,Matrix.adjugate_diagonal]
  apply congrArg Matrix.diagonal
  funext i
  by_cases hi : i=Fin.last (3*q)
  · subst i; simp
  · rw [if_neg hi]
    apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hi,Finset.mem_univ _⟩)
    simp

theorem threeOne_shift_scalarU (q : ℕ) (a b : Fin 3) (ha : a≠0) :
    observabilityScalarU (threeOneShiftM (R:=R) q)
      (observabilitySelectedMatrix (threeOneShiftM q) (threeOneShiftP q)
        (threeOneLevel q) (threeOneRow q a)).adjugate
      (threeOneLevel q) (threeOneRow q a) 0 b=if b=a then 1 else 0 := by
  rw [threeOne_shift_selected_adjugate q a ha]
  simp only [observabilityScalarU,Matrix.sum_apply,Matrix.mul_apply,
    observabilityScalarColumn,Matrix.diagonal_apply]
  rw [Finset.sum_eq_single (Fin.last (3*q))]
  · simp [threeOneShiftM,finiteShiftMatrix_pow,finiteShiftMatrix,ite_mul]
  · intro k _ hk
    apply Finset.sum_eq_zero
    intro l _
    by_cases hl : l=k
    · subst l; simp [hk]
    · simp [hl]
  · simp

end FD56
