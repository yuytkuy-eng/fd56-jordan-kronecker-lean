/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Data.Matrix.Block
import Mathlib.Tactic

/-! Constant corrections separate unequal poles without division by two. -/

noncomputable section
namespace FD56
open Matrix

variable {K n : Type*} [Field K] [LinearOrder n]

def regularPoleCorrection (lam : n → K) (A B : Matrix n n K) : Matrix n n K := by
  classical
  exact fun i j => if lam i = lam j then (if i < j then -B i j else 0)
    else (A i j+lam j*B i j)/(lam i-lam j)

def regularPoleResidual (lam : n → K) (A B : Matrix n n K) : Matrix n n K := by
  classical
  exact fun i j => if lam i = lam j then A i j+lam i*B i j else 0

theorem regularPoleCorrection_entries (lam : n → K) (A B : Matrix n n K)
    (hA : A.transpose = -A) (hB : B.transpose = -B) (hBd : ∀ i, B i i = 0)
    (i j : n) :
    B i j + regularPoleCorrection lam A B i j - regularPoleCorrection lam A B j i = 0 ∧
    A i j - lam i*regularPoleCorrection lam A B i j +
      lam j*regularPoleCorrection lam A B j i = regularPoleResidual lam A B i j := by
  classical
  have hAj : A j i = -A i j := congrArg (fun M => M i j) hA
  have hBj : B j i = -B i j := congrArg (fun M => M i j) hB
  by_cases hl : lam i = lam j
  · rcases lt_trichotomy i j with hij | rfl | hji
    · simp only [regularPoleCorrection,regularPoleResidual,if_pos hl,if_pos hl.symm,
        if_pos hij,if_neg (not_lt_of_ge (le_of_lt hij))]
      constructor <;> ring
    · simp [regularPoleCorrection,regularPoleResidual,hBd]
    · simp only [regularPoleCorrection,regularPoleResidual,if_pos hl,if_pos hl.symm,
        if_pos hji,if_neg (not_lt_of_ge (le_of_lt hji)),hBj]
      rw [hl]
      constructor <;> ring
  · simp only [regularPoleCorrection,regularPoleResidual,if_neg hl,if_neg (Ne.symm hl),hAj,hBj]
    constructor <;> field_simp [sub_ne_zero.mpr hl,sub_ne_zero.mpr (Ne.symm hl)] <;> ring

variable [Fintype n]

omit [Fintype n] in
theorem regularPoleCorrection_linear (lam : n → K) (A B : Matrix n n K)
    (hA : A.transpose = -A) (hB : B.transpose = -B) (hBd : ∀ i, B i i = 0) :
    B + regularPoleCorrection lam A B - (regularPoleCorrection lam A B).transpose = 0 := by
  ext i j
  exact (regularPoleCorrection_entries lam A B hA hB hBd i j).1

theorem regularPoleCorrection_constant (lam : n → K) (A B : Matrix n n K)
    (hA : A.transpose = -A) (hB : B.transpose = -B) (hBd : ∀ i, B i i = 0) :
    A - Matrix.diagonal lam * regularPoleCorrection lam A B +
      (regularPoleCorrection lam A B).transpose * Matrix.diagonal lam =
        regularPoleResidual lam A B := by
  ext i j
  simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.diagonal_mul,Matrix.mul_diagonal,
    Matrix.transpose_apply]
  simpa only [mul_comm] using (regularPoleCorrection_entries lam A B hA hB hBd i j).2

end FD56
