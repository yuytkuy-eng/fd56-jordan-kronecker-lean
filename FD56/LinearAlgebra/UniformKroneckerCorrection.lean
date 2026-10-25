/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Tactic

/-! Simultaneous correction of alternating complement blocks without division by two.

Block indices are chain degrees. For `a,b >= 1`, the correction satisfies
`X a b - (X b a).transpose = S a b` and
`X (a-1) b - (X (b-1) a).transpose = -T a b`.
These are exactly the equations for killing the two complement-complement
blocks when the cross blocks are respectively the identity shift and its
negative predecessor shift. This module does not construct kernel chains.
-/

namespace FD56
open Matrix

variable {R : Type*} [CommRing R] {r : ℕ}

def alternatingUpperPart (A : Matrix (Fin r) (Fin r) R) : Matrix (Fin r) (Fin r) R :=
  fun i j => if i < j then A i j else 0

theorem alternatingUpperPart_sub_transpose
    (A : Matrix (Fin r) (Fin r) R)
    (hskew : A.transpose = -A) (hdiag : ∀ i, A i i = 0) :
    alternatingUpperPart A - (alternatingUpperPart A).transpose = A := by
  funext i j
  rcases lt_trichotomy i j with h | h | h
  · simp [alternatingUpperPart,h,not_lt_of_ge h.le]
  · subst j
    simp [alternatingUpperPart,hdiag]
  · have hs := congrArg (fun B : Matrix (Fin r) (Fin r) R => B i j) hskew
    simpa [alternatingUpperPart,h,not_lt_of_ge h.le] using congrArg Neg.neg hs

def uniformCorrectionUpper
    (S T : ℕ → ℕ → Matrix (Fin r) (Fin r) R) (a b : ℕ) : Matrix (Fin r) (Fin r) R :=
  if _h : a + 1 < b then
    uniformCorrectionUpper S T (a+1) (b-1) - S (a+1) (b-1) - T (a+1) b
  else if a = b then alternatingUpperPart (S a a)
  else alternatingUpperPart (-T b b)
termination_by b
decreasing_by omega

def uniformKroneckerCorrection
    (S T : ℕ → ℕ → Matrix (Fin r) (Fin r) R) (a b : ℕ) : Matrix (Fin r) (Fin r) R :=
  if a ≤ b then uniformCorrectionUpper S T a b
  else (uniformCorrectionUpper S T b a).transpose - (S b a).transpose

theorem uniformCorrectionUpper_diagonal
    (S T : ℕ → ℕ → Matrix (Fin r) (Fin r) R) (a : ℕ) :
    uniformCorrectionUpper S T a a = alternatingUpperPart (S a a) := by
  rw [uniformCorrectionUpper]
  simp

theorem uniformCorrectionUpper_successor
    (S T : ℕ → ℕ → Matrix (Fin r) (Fin r) R) (a : ℕ) :
    uniformCorrectionUpper S T a (a+1) = alternatingUpperPart (-T (a+1) (a+1)) := by
  rw [uniformCorrectionUpper]
  simp

theorem uniformKroneckerCorrection_first
    (S T : ℕ → ℕ → Matrix (Fin r) (Fin r) R)
    (hS : ∀ a b, (S b a).transpose = -S a b)
    (hSd : ∀ a i, S a a i i = 0) (a b : ℕ) :
    uniformKroneckerCorrection S T a b - (uniformKroneckerCorrection S T b a).transpose =
      S a b := by
  rcases lt_trichotomy a b with h | h | h
  · simp only [uniformKroneckerCorrection,if_pos h.le,if_neg (not_le_of_gt h),
      Matrix.transpose_sub,Matrix.transpose_transpose]
    abel
  · subst b
    simp only [uniformKroneckerCorrection,le_refl,if_true,uniformCorrectionUpper_diagonal]
    exact alternatingUpperPart_sub_transpose _ (hS a a) (hSd a)
  · simp only [uniformKroneckerCorrection,if_neg (not_le_of_gt h),if_pos h.le]
    rw [hS]
    abel

private theorem uniformKroneckerCorrection_second_of_le
    (S T : ℕ → ℕ → Matrix (Fin r) (Fin r) R)
    (hS : ∀ a b, (S b a).transpose = -S a b)
    (hSd : ∀ a i, S a a i i = 0)
    (hT : ∀ a b, (T b a).transpose = -T a b)
    (hTd : ∀ a i, T a a i i = 0)
    (a b : ℕ) (ha : 0 < a) (hab : a ≤ b) :
    uniformKroneckerCorrection S T (a-1) b -
        (uniformKroneckerCorrection S T (b-1) a).transpose = -T a b := by
  rcases hab.eq_or_lt with h | h
  · subst b
    have hae : a-1+1=a := by omega
    have hle : a-1 ≤ a := by omega
    simp only [uniformKroneckerCorrection,if_pos hle]
    have hu : uniformCorrectionUpper S T (a-1) a = alternatingUpperPart (-T a a) := by
      simpa only [hae] using uniformCorrectionUpper_successor S T (a-1)
    rw [hu]
    apply alternatingUpperPart_sub_transpose
    · simpa only [Matrix.transpose_neg,neg_neg] using congrArg Neg.neg (hT a a)
    · intro i
      simp [hTd]
  · have ha' : a-1+1=a := by omega
    have hab' : a ≤ b-1 := by omega
    have hlow : a-1 ≤ b := by omega
    have hrec : uniformKroneckerCorrection S T (a-1) b =
        uniformKroneckerCorrection S T a (b-1) - S a (b-1) - T a b := by
      simp only [uniformKroneckerCorrection,if_pos hlow,if_pos hab']
      rw [uniformCorrectionUpper,dif_pos (by omega : a-1+1 < b),ha']
    have hfirst := uniformKroneckerCorrection_first S T hS hSd a (b-1)
    rw [hrec]
    rw [← hfirst]
    abel

theorem uniformKroneckerCorrection_second
    (S T : ℕ → ℕ → Matrix (Fin r) (Fin r) R)
    (hS : ∀ a b, (S b a).transpose = -S a b)
    (hSd : ∀ a i, S a a i i = 0)
    (hT : ∀ a b, (T b a).transpose = -T a b)
    (hTd : ∀ a i, T a a i i = 0)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    uniformKroneckerCorrection S T (a-1) b -
        (uniformKroneckerCorrection S T (b-1) a).transpose = -T a b := by
  by_cases hab : a ≤ b
  · exact uniformKroneckerCorrection_second_of_le S T hS hSd hT hTd a b ha hab
  · have h := uniformKroneckerCorrection_second_of_le S T hS hSd hT hTd b a hb
      (Nat.le_of_lt (Nat.lt_of_not_ge hab))
    have ht := congrArg Matrix.transpose h
    simp only [Matrix.transpose_sub,Matrix.transpose_transpose,Matrix.transpose_neg,hT,neg_neg] at ht
    rw [← ht]
    abel

end FD56
