/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.UniformKroneckerCongruence

/-! Mixed chain correction by zero extension to equal-length chains and
restriction of the uniform correction. This construction uses no division. -/

namespace FD56
open Matrix

variable {R : Type*} [CommRing R] {r : ℕ}

def mixedNext {d : Fin r → ℕ} (a : Σ j, Fin (d j)) : Σ j, Fin (d j+1) :=
  ⟨a.1,a.2.succ⟩

def mixedCurrent {d : Fin r → ℕ} (a : Σ j, Fin (d j)) : Σ j, Fin (d j+1) :=
  ⟨a.1,a.2.castSucc⟩

def mixedCrossFirst (d : Fin r → ℕ) :
    Matrix (Σ j, Fin (d j+1)) (Σ j, Fin (d j)) R :=
  (1 : Matrix (Σ j, Fin (d j+1)) (Σ j, Fin (d j+1)) R).submatrix id mixedNext

def mixedCrossSecond (d : Fin r → ℕ) :
    Matrix (Σ j, Fin (d j+1)) (Σ j, Fin (d j)) R :=
  -(1 : Matrix (Σ j, Fin (d j+1)) (Σ j, Fin (d j+1)) R).submatrix id mixedCurrent

def mixedMaxDegree (d : Fin r → ℕ) : ℕ := Finset.univ.sup d

theorem le_mixedMaxDegree (d : Fin r → ℕ) (j : Fin r) : d j ≤ mixedMaxDegree d :=
  Finset.le_sup (Finset.mem_univ j)

def mixedUniformCoefficientIndex (d : Fin r → ℕ) (a : Σ j, Fin (d j+1)) :
    Fin (mixedMaxDegree d+1) × Fin r :=
  (⟨a.2.val, by have := a.2.isLt; have := le_mixedMaxDegree d a.1; omega⟩,a.1)

def mixedUniformFunctionalIndex (d : Fin r → ℕ) (a : Σ j, Fin (d j)) :
    Fin (mixedMaxDegree d) × Fin r :=
  (⟨a.2.val, lt_of_lt_of_le a.2.isLt (le_mixedMaxDegree d a.1)⟩,a.1)

theorem mixedUniformCoefficientIndex_next (d : Fin r → ℕ) (a : Σ j, Fin (d j)) :
    mixedUniformCoefficientIndex d (mixedNext a) =
      uniformNext (mixedUniformFunctionalIndex d a) := rfl

theorem mixedUniformCoefficientIndex_current (d : Fin r → ℕ) (a : Σ j, Fin (d j)) :
    mixedUniformCoefficientIndex d (mixedCurrent a) =
      uniformCurrent (mixedUniformFunctionalIndex d a) := rfl

def mixedBlockPadding (d : Fin r → ℕ) (S : Matrix (Σ j, Fin (d j)) (Σ j, Fin (d j)) R) :
    Matrix (Fin (mixedMaxDegree d) × Fin r) (Fin (mixedMaxDegree d) × Fin r) R := fun a b =>
  if ha : a.1.val < d a.2 then
    if hb : b.1.val < d b.2 then S ⟨a.2,⟨a.1.val,ha⟩⟩ ⟨b.2,⟨b.1.val,hb⟩⟩ else 0
  else 0

theorem mixedBlockPadding_apply (d : Fin r → ℕ)
    (S : Matrix (Σ j, Fin (d j)) (Σ j, Fin (d j)) R) (a b : Σ j, Fin (d j)) :
    mixedBlockPadding d S (mixedUniformFunctionalIndex d a) (mixedUniformFunctionalIndex d b) = S a b := by
  simp [mixedBlockPadding, mixedUniformFunctionalIndex, a.2.isLt, b.2.isLt]

theorem mixedBlockPadding_skew (d : Fin r → ℕ)
    (S : Matrix (Σ j, Fin (d j)) (Σ j, Fin (d j)) R) (hS : S.transpose = -S) :
    (mixedBlockPadding d S).transpose = -mixedBlockPadding d S := by
  funext a b
  by_cases ha : a.1.val < d a.2 <;> by_cases hb : b.1.val < d b.2 <;>
    simp [mixedBlockPadding, ha, hb, Matrix.transpose_apply, Matrix.neg_apply]
  exact congrArg (fun M => M ⟨a.2,⟨a.1.val,ha⟩⟩ ⟨b.2,⟨b.1.val,hb⟩⟩) hS

theorem mixedBlockPadding_diag (d : Fin r → ℕ)
    (S : Matrix (Σ j, Fin (d j)) (Σ j, Fin (d j)) R) (hS : ∀ i, S i i = 0) :
    ∀ i, mixedBlockPadding d S i i = 0 := by
  intro i
  by_cases hi : i.1.val < d i.2 <;> simp [mixedBlockPadding, hi, hS]

def mixedFiniteCorrection (d : Fin r → ℕ)
    (S T : Matrix (Σ j, Fin (d j)) (Σ j, Fin (d j)) R) :
    Matrix (Σ j, Fin (d j+1)) (Σ j, Fin (d j)) R :=
  (uniformFiniteCorrection (mixedBlockPadding d S) (mixedBlockPadding d T)).submatrix
    (mixedUniformCoefficientIndex d) (mixedUniformFunctionalIndex d)

theorem mixedFiniteCorrection_first (d : Fin r → ℕ)
    (S T : Matrix (Σ j, Fin (d j)) (Σ j, Fin (d j)) R)
    (hS : S.transpose = -S) (hSd : ∀ i, S i i = 0) :
    (mixedFiniteCorrection d S T).submatrix mixedNext id -
      ((mixedFiniteCorrection d S T).submatrix mixedNext id).transpose = S := by
  funext a b
  have h := congrArg (fun M => M (mixedUniformFunctionalIndex d a) (mixedUniformFunctionalIndex d b))
    (uniformFiniteCorrection_first (mixedBlockPadding d S) (mixedBlockPadding d T)
      (mixedBlockPadding_skew d S hS) (mixedBlockPadding_diag d S hSd))
  simpa only [Matrix.sub_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
    mixedFiniteCorrection, mixedUniformCoefficientIndex_next, id_eq, mixedBlockPadding_apply] using h

theorem mixedFiniteCorrection_second (d : Fin r → ℕ)
    (S T : Matrix (Σ j, Fin (d j)) (Σ j, Fin (d j)) R)
    (hS : S.transpose = -S) (hSd : ∀ i, S i i = 0)
    (hT : T.transpose = -T) (hTd : ∀ i, T i i = 0) :
    (mixedFiniteCorrection d S T).submatrix mixedCurrent id -
      ((mixedFiniteCorrection d S T).submatrix mixedCurrent id).transpose = -T := by
  funext a b
  have h := congrArg (fun M => M (mixedUniformFunctionalIndex d a) (mixedUniformFunctionalIndex d b))
    (uniformFiniteCorrection_second (mixedBlockPadding d S) (mixedBlockPadding d T)
      (mixedBlockPadding_skew d S hS) (mixedBlockPadding_diag d S hSd)
      (mixedBlockPadding_skew d T hT) (mixedBlockPadding_diag d T hTd))
  simpa only [Matrix.sub_apply, Matrix.transpose_apply, Matrix.neg_apply, Matrix.submatrix_apply,
    mixedFiniteCorrection, mixedUniformCoefficientIndex_current, id_eq, mixedBlockPadding_apply] using h

theorem mixedCrossFirst_transpose_mul (d : Fin r → ℕ)
    (X : Matrix (Σ j, Fin (d j+1)) (Σ j, Fin (d j)) R) :
    (mixedCrossFirst d).transpose * X = X.submatrix mixedNext id := by
  simp only [mixedCrossFirst, Matrix.transpose_submatrix, Matrix.transpose_one]
  simpa using Matrix.one_submatrix_mul mixedNext (Equiv.refl _) X

theorem mixedCrossSecond_transpose_mul (d : Fin r → ℕ)
    (X : Matrix (Σ j, Fin (d j+1)) (Σ j, Fin (d j)) R) :
    (mixedCrossSecond d).transpose * X = -(X.submatrix mixedCurrent id) := by
  simp only [mixedCrossSecond, Matrix.transpose_neg, Matrix.transpose_submatrix,
    Matrix.transpose_one, Matrix.neg_mul]
  congr 1
  simpa using Matrix.one_submatrix_mul mixedCurrent (Equiv.refl _) X

/-- Restricting the padded correction gives an explicit invertible constant
congruence for arbitrary mixed chain lengths, including characteristic two. -/
theorem mixed_kronecker_block_congruence (d : Fin r → ℕ)
    (S T : Matrix (Σ j, Fin (d j)) (Σ j, Fin (d j)) R)
    (hS : S.transpose = -S) (hSd : ∀ i, S i i = 0)
    (hT : T.transpose = -T) (hTd : ∀ i, T i i = 0) :
    let X := mixedFiniteCorrection d S T
    complementShift X * complementShift (-X) = 1 ∧
    complementShift (-X) * complementShift X = 1 ∧
    (complementShift X).transpose * Matrix.fromBlocks 0 (mixedCrossFirst d)
      (-(mixedCrossFirst d).transpose) S * complementShift X =
        Matrix.fromBlocks 0 (mixedCrossFirst d) (-(mixedCrossFirst d).transpose) 0 ∧
    (complementShift X).transpose * Matrix.fromBlocks 0 (mixedCrossSecond d)
      (-(mixedCrossSecond d).transpose) T * complementShift X =
        Matrix.fromBlocks 0 (mixedCrossSecond d) (-(mixedCrossSecond d).transpose) 0 := by
  dsimp only
  refine ⟨complementShift_inverse _, ?_, ?_, ?_⟩
  · simpa only [neg_neg] using complementShift_inverse (-mixedFiniteCorrection d S T)
  · apply complementShift_congruence
    rw [show (mixedFiniteCorrection d S T).transpose * mixedCrossFirst d =
        ((mixedCrossFirst d).transpose * mixedFiniteCorrection d S T).transpose by simp]
    rw [mixedCrossFirst_transpose_mul]
    exact mixedFiniteCorrection_first d S T hS hSd
  · apply complementShift_congruence
    rw [show (mixedFiniteCorrection d S T).transpose * mixedCrossSecond d =
        ((mixedCrossSecond d).transpose * mixedFiniteCorrection d S T).transpose by simp]
    rw [mixedCrossSecond_transpose_mul, Matrix.transpose_neg]
    have h := mixedFiniteCorrection_second d S T hS hSd hT hTd
    calc
      _ = -((mixedFiniteCorrection d S T).submatrix mixedCurrent id -
          ((mixedFiniteCorrection d S T).submatrix mixedCurrent id).transpose) := by abel
      _ = T := by rw [h, neg_neg]

end FD56
