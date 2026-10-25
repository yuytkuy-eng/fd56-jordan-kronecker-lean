/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.UniformKroneckerCorrection
import Mathlib.Data.Matrix.Block

/-! Finite uniform-chain correction and an explicit invertible constant congruence.

Indices are degree first and chain second. The coefficient span has index
`Fin (e+1) × Fin r`; its chosen dual complement has index `Fin e × Fin r`.
The cross blocks are respectively the successor inclusion and the negative
current-degree inclusion. The hypotheses explicitly supply the zero block
on the coefficient span and these cross blocks.
-/

namespace FD56
open Matrix

variable {R : Type*} [CommRing R] {e r : ℕ}

def uniformBlockExtension (S : Matrix (Fin e × Fin r) (Fin e × Fin r) R)
    (a b : ℕ) : Matrix (Fin r) (Fin r) R := fun i j =>
  if ha : 0 < a ∧ a ≤ e then
    if hb : 0 < b ∧ b ≤ e then
      S (⟨a-1,by omega⟩,i) (⟨b-1,by omega⟩,j)
    else 0
  else 0

theorem uniformBlockExtension_succ
    (S : Matrix (Fin e × Fin r) (Fin e × Fin r) R)
    (a b : Fin e) (i j : Fin r) :
    uniformBlockExtension S (a.val+1) (b.val+1) i j = S (a,i) (b,j) := by
  simp [uniformBlockExtension,a.isLt,b.isLt,Nat.succ_le_iff]

theorem uniformBlockExtension_skew
    (S : Matrix (Fin e × Fin r) (Fin e × Fin r) R) (hS : S.transpose = -S) :
    ∀ a b, (uniformBlockExtension S b a).transpose = -uniformBlockExtension S a b := by
  intro a b
  funext i j
  by_cases ha : 0 < a ∧ a ≤ e <;> by_cases hb : 0 < b ∧ b ≤ e <;>
    simp [uniformBlockExtension,ha,hb,Matrix.transpose_apply,Matrix.neg_apply]
  exact congrArg (fun A => A (⟨a-1,by omega⟩,i) (⟨b-1,by omega⟩,j)) hS

theorem uniformBlockExtension_diag
    (S : Matrix (Fin e × Fin r) (Fin e × Fin r) R) (hS : ∀ i, S i i = 0) :
    ∀ a i, uniformBlockExtension S a a i i = 0 := by
  intro a i
  by_cases ha : 0 < a ∧ a ≤ e <;> simp [uniformBlockExtension,ha,hS]

def uniformNext (a : Fin e × Fin r) : Fin (e+1) × Fin r := (a.1.succ,a.2)
def uniformCurrent (a : Fin e × Fin r) : Fin (e+1) × Fin r := (a.1.castSucc,a.2)

def uniformFiniteCorrection
    (S T : Matrix (Fin e × Fin r) (Fin e × Fin r) R) :
    Matrix (Fin (e+1) × Fin r) (Fin e × Fin r) R := fun ai bj =>
  uniformKroneckerCorrection (uniformBlockExtension S) (uniformBlockExtension T)
    ai.1.val (bj.1.val+1) ai.2 bj.2

theorem uniformFiniteCorrection_first
    (S T : Matrix (Fin e × Fin r) (Fin e × Fin r) R)
    (hS : S.transpose = -S) (hSd : ∀ i, S i i = 0) :
    (uniformFiniteCorrection S T).submatrix uniformNext id -
      ((uniformFiniteCorrection S T).submatrix uniformNext id).transpose = S := by
  funext ai bj
  have h := uniformKroneckerCorrection_first (uniformBlockExtension S) (uniformBlockExtension T)
    (uniformBlockExtension_skew S hS) (uniformBlockExtension_diag S hSd)
    (ai.1.val+1) (bj.1.val+1)
  have hh := congrArg (fun A => A ai.2 bj.2) h
  simpa only [Matrix.sub_apply,Matrix.transpose_apply,uniformBlockExtension_succ,
    Matrix.submatrix_apply,uniformFiniteCorrection,uniformNext,Fin.val_succ,id_eq] using hh

theorem uniformFiniteCorrection_second
    (S T : Matrix (Fin e × Fin r) (Fin e × Fin r) R)
    (hS : S.transpose = -S) (hSd : ∀ i, S i i = 0)
    (hT : T.transpose = -T) (hTd : ∀ i, T i i = 0) :
    (uniformFiniteCorrection S T).submatrix uniformCurrent id -
      ((uniformFiniteCorrection S T).submatrix uniformCurrent id).transpose = -T := by
  funext ai bj
  have h := uniformKroneckerCorrection_second (uniformBlockExtension S) (uniformBlockExtension T)
    (uniformBlockExtension_skew S hS) (uniformBlockExtension_diag S hSd)
    (uniformBlockExtension_skew T hT) (uniformBlockExtension_diag T hTd)
    (ai.1.val+1) (bj.1.val+1) (by omega) (by omega)
  have hh := congrArg (fun A => A ai.2 bj.2) h
  simpa only [Matrix.sub_apply,Matrix.transpose_apply,Matrix.neg_apply,
    uniformBlockExtension_succ,Matrix.submatrix_apply,uniformFiniteCorrection,
    uniformCurrent,Nat.add_sub_cancel,id_eq] using hh

def uniformCrossFirst : Matrix (Fin (e+1) × Fin r) (Fin e × Fin r) R :=
  (1 : Matrix (Fin (e+1) × Fin r) (Fin (e+1) × Fin r) R).submatrix id uniformNext

def uniformCrossSecond : Matrix (Fin (e+1) × Fin r) (Fin e × Fin r) R :=
  -(1 : Matrix (Fin (e+1) × Fin r) (Fin (e+1) × Fin r) R).submatrix id uniformCurrent

theorem uniformCrossFirst_transpose_mul
    (X : Matrix (Fin (e+1) × Fin r) (Fin e × Fin r) R) :
    uniformCrossFirst.transpose * X = X.submatrix uniformNext id := by
  simp only [uniformCrossFirst,Matrix.transpose_submatrix,Matrix.transpose_one]
  simpa using Matrix.one_submatrix_mul uniformNext (Equiv.refl _) X

theorem uniformCrossSecond_transpose_mul
    (X : Matrix (Fin (e+1) × Fin r) (Fin e × Fin r) R) :
    uniformCrossSecond.transpose * X = -(X.submatrix uniformCurrent id) := by
  simp only [uniformCrossSecond,Matrix.transpose_neg,Matrix.transpose_submatrix,
    Matrix.transpose_one,Matrix.neg_mul]
  congr 1
  simpa using Matrix.one_submatrix_mul uniformCurrent (Equiv.refl _) X

def complementShift {w f : Type*} [Fintype w] [Fintype f] [DecidableEq w] [DecidableEq f]
    (X : Matrix w f R) : Matrix (w ⊕ f) (w ⊕ f) R :=
  Matrix.fromBlocks 1 X 0 1

theorem complementShift_inverse {w f : Type*} [Fintype w] [Fintype f]
    [DecidableEq w] [DecidableEq f] (X : Matrix w f R) :
    complementShift X * complementShift (-X) = 1 := by
  simp [complementShift,Matrix.fromBlocks_multiply,Matrix.fromBlocks_one]

theorem complementShift_congruence {w f : Type*} [Fintype w] [Fintype f]
    [DecidableEq w] [DecidableEq f] (C X : Matrix w f R) (S : Matrix f f R)
    (hX : C.transpose * X - X.transpose * C = S) :
    (complementShift X).transpose * Matrix.fromBlocks 0 C (-C.transpose) S * complementShift X =
      Matrix.fromBlocks 0 C (-C.transpose) 0 := by
  simp only [complementShift,Matrix.fromBlocks_transpose,Matrix.transpose_one,
    Matrix.transpose_zero,Matrix.fromBlocks_multiply,Matrix.mul_zero,Matrix.zero_mul,
    Matrix.one_mul,Matrix.mul_one,zero_add,add_zero,Matrix.neg_mul]
  rw [← hX]
  abel_nf

theorem uniform_kronecker_block_congruence
    (S T : Matrix (Fin e × Fin r) (Fin e × Fin r) R)
    (hS : S.transpose = -S) (hSd : ∀ i, S i i = 0)
    (hT : T.transpose = -T) (hTd : ∀ i, T i i = 0) :
    let X := uniformFiniteCorrection S T
    complementShift X * complementShift (-X) = 1 ∧
    complementShift (-X) * complementShift X = 1 ∧
    (complementShift X).transpose * Matrix.fromBlocks 0 uniformCrossFirst
      (-uniformCrossFirst.transpose) S * complementShift X =
        Matrix.fromBlocks 0 uniformCrossFirst (-uniformCrossFirst.transpose) 0 ∧
    (complementShift X).transpose * Matrix.fromBlocks 0 uniformCrossSecond
      (-uniformCrossSecond.transpose) T * complementShift X =
        Matrix.fromBlocks 0 uniformCrossSecond (-uniformCrossSecond.transpose) 0 := by
  dsimp only
  refine ⟨complementShift_inverse _,?_,?_,?_⟩
  · simpa only [neg_neg] using complementShift_inverse (-uniformFiniteCorrection S T)
  · apply complementShift_congruence
    rw [show (uniformFiniteCorrection S T).transpose * uniformCrossFirst =
        (uniformCrossFirst.transpose * uniformFiniteCorrection S T).transpose by simp]
    rw [uniformCrossFirst_transpose_mul]
    exact uniformFiniteCorrection_first S T hS hSd
  · apply complementShift_congruence
    rw [show (uniformFiniteCorrection S T).transpose * uniformCrossSecond =
        (uniformCrossSecond.transpose * uniformFiniteCorrection S T).transpose by simp]
    rw [uniformCrossSecond_transpose_mul,Matrix.transpose_neg]
    have h := uniformFiniteCorrection_second S T hS hSd hT hTd
    calc
      _ = -((uniformFiniteCorrection S T).submatrix uniformCurrent id -
          ((uniformFiniteCorrection S T).submatrix uniformCurrent id).transpose) := by abel
      _ = T := by rw [h,neg_neg]

end FD56
