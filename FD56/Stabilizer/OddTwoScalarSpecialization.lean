/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.OddTwoObservabilitySelectors
import FD56.LinearAlgebra.FiniteShiftMatrix

/-! A sparse specialization separates the two odd-dimensional scalar lifts. -/

namespace FD56
open Matrix
open scoped BigOperators
variable {R : Type*} [CommRing R]

def oddTwoShiftM (q : ℕ) : Matrix (Fin (2*q+1)) (Fin (2*q+1)) R :=
  finiteShiftMatrix (2*q+1) 2

def oddTwoShiftP (q : ℕ) : Matrix (Fin 2) (Fin (2*q+1)) R :=
  finiteInitialRows 2 (2*q+1)

theorem oddTwo_shift_selected_zero (q : ℕ) :
    observabilitySelectedMatrix (oddTwoShiftM (R := R) q) (oddTwoShiftP q)
      (oddTwoLevel q) (oddTwoRow q 0)=1 := by
  ext i j
  simp only [observabilitySelectedMatrix,oddTwoShiftM,oddTwoShiftP,
    finiteShiftMatrix_pow,finiteInitialRows_mul_shift]
  rw [finiteInitialRows_mul_shift]
  dsimp only
  have hi : (oddTwoRow q 0 i).val+2*oddTwoLevel q i=i.val := by
    by_cases h : i.val=2*q
    · simp [oddTwoRow,oddTwoLevel,h]
    · simp only [oddTwoRow,h,↓reduceIte,oddTwoLevel]
      omega
  rw [hi]
  simp [Matrix.one_apply,Fin.ext_iff]

theorem oddTwo_shift_selected_one (q : ℕ) :
    observabilitySelectedMatrix (oddTwoShiftM (R := R) q) (oddTwoShiftP q)
      (oddTwoLevel q) (oddTwoRow q 1)=
      Matrix.diagonal (fun i : Fin (2*q+1) => if i=Fin.last (2*q) then (0 : R) else 1) := by
  ext i j
  simp only [observabilitySelectedMatrix,oddTwoShiftM,oddTwoShiftP,
    finiteShiftMatrix_pow,finiteInitialRows_mul_shift]
  rw [finiteInitialRows_mul_shift]
  dsimp only
  by_cases h : i.val=2*q
  · have hi : i=Fin.last (2*q) := Fin.ext h
    have hj : 1+2*q ≠ j.val := by omega
    simp [oddTwoRow,oddTwoLevel,h,hi,Matrix.diagonal_apply,hj]
  · have hi : i ≠ Fin.last (2*q) := by intro he; exact h (congrArg Fin.val he)
    have he : (oddTwoRow q 1 i).val+2*oddTwoLevel q i=i.val := by
      simp only [oddTwoRow,h,↓reduceIte,oddTwoLevel]
      omega
    rw [he]
    simp [Matrix.diagonal_apply,hi,Fin.ext_iff,h]

theorem oddTwo_shift_selected_one_adjugate (q : ℕ) :
    (observabilitySelectedMatrix (oddTwoShiftM (R := R) q) (oddTwoShiftP q)
      (oddTwoLevel q) (oddTwoRow q 1)).adjugate=
      Matrix.diagonal (fun i : Fin (2*q+1) => if i=Fin.last (2*q) then (1 : R) else 0) := by
  rw [oddTwo_shift_selected_one,Matrix.adjugate_diagonal]
  apply congrArg Matrix.diagonal
  funext i
  by_cases hi : i=Fin.last (2*q)
  · subst i
    simp
  · rw [if_neg hi]
    apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hi,Finset.mem_univ _⟩)
    simp

theorem oddTwo_shift_selected_zero_det (q : ℕ) :
    (observabilitySelectedMatrix (oddTwoShiftM (R := R) q) (oddTwoShiftP q)
      (oddTwoLevel q) (oddTwoRow q 0)).det=1 := by
  rw [oddTwo_shift_selected_zero,Matrix.det_one]

theorem oddTwo_shift_selected_one_det (q : ℕ) :
    (observabilitySelectedMatrix (oddTwoShiftM (R := R) q) (oddTwoShiftP q)
      (oddTwoLevel q) (oddTwoRow q 1)).det=0 := by
  rw [oddTwo_shift_selected_one,Matrix.det_diagonal]
  apply Finset.prod_eq_zero (Finset.mem_univ (Fin.last (2*q)))
  simp

theorem oddTwo_shift_scalarU_one (q : ℕ) :
    observabilityScalarU (oddTwoShiftM (R := R) q)
      (observabilitySelectedMatrix (oddTwoShiftM q) (oddTwoShiftP q)
        (oddTwoLevel q) (oddTwoRow q 1)).adjugate
      (oddTwoLevel q) (oddTwoRow q 1) 0 1=1 := by
  rw [oddTwo_shift_selected_one_adjugate]
  simp only [observabilityScalarU,Matrix.sum_apply,Matrix.mul_apply,
    observabilityScalarColumn,Matrix.diagonal_apply]
  rw [Finset.sum_eq_single (Fin.last (2*q))]
  · simp [oddTwoShiftM,finiteShiftMatrix_pow,finiteShiftMatrix,ite_mul]
  · intro k _ hk
    apply Finset.sum_eq_zero
    intro l _
    by_cases hl : l=k
    · subst l
      simp [hk]
    · simp [hl]
  · simp

end FD56
