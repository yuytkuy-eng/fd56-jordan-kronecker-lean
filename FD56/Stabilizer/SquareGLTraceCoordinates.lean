/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.SquareGLDiagonalPoles
import FD56.Stabilizer.GLSquareBasisChange

/-! Exact trace coordinates through the constant square GL normalization.
These identities identify the hyperplane needed for the SL restriction. -/

noncomputable section
namespace FD56
open Matrix
open scoped BigOperators

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

theorem glSquareBasisChange_trace (S T W : Matrix n n R) (hTS : T*S=1)
    (v : SLInput n n → R) :
    Matrix.trace (matrixPairEquiv R R n n (glSquareBasisChange S T W *ᵥ v)).1 =
      Matrix.trace (matrixPairEquiv R R n n v).1 := by
  rw [glSquareBasisChange_mulVec]
  change Matrix.trace (S*(matrixPairEquiv R R n n v).1*T) = _
  rw [Matrix.trace_mul_cycle, hTS, Matrix.one_mul]

theorem lowerBlockShift_top (Z : Matrix n n R) (v : n ⊕ n → R) (i : n) :
    (lowerBlockShift Z *ᵥ v) (.inl i) = v (.inl i) := by
  simp [lowerBlockShift,Matrix.fromBlocks_mulVec]

theorem squareGLPartnerSign_trace (v : SLInput n n → R) :
    Matrix.trace (matrixPairEquiv R R n n
      ((squareGLPartnerSign (R := R) (n := n)).submatrix (squareGLPoleIndex n).symm id *ᵥ v)).1 =
      ∑ i, v (.inl (i,i)) := by
  unfold Matrix.trace Matrix.diag
  apply Finset.sum_congr rfl
  intro i _
  change ((squareGLPartnerSign (R := R) (n := n)).submatrix
    (squareGLPoleIndex n).symm id *ᵥ v) (.inl (i,i)) = _
  change (squareGLPartnerSign (R := R) (n := n) *ᵥ v)
    ((squareGLPoleIndex n).symm (.inl (i,i))) = _
  simp [squareGLPoleIndex,squareGLPartnerSign,Matrix.fromBlocks_mulVec]

theorem squareGL_pole_trace_coordinate (Z : Matrix (n × n) (n × n) R)
    (v : ((n ⊕ n) × n) → R) :
    Matrix.trace (matrixPairEquiv R R n n
      (((squareGLPartnerSign (R := R) (n := n)).submatrix (squareGLPoleIndex n).symm id *
        (lowerBlockShift Z).submatrix id (Equiv.sumProdDistrib n n n)) *ᵥ v)).1 =
      ∑ i, v (.inl i,i) := by
  rw [← Matrix.mulVec_mulVec,squareGLPartnerSign_trace,Matrix.submatrix_mulVec_equiv]
  simp only [Function.comp_apply,id_eq,lowerBlockShift_top]
  rfl

variable {K : Type*} [Field K]

theorem rankTwoCoordinateChange_pivot (c : K) (w : n → K) (v : Fin 2 ⊕ n → K) :
    (rankTwoCoordinateChange c w *ᵥ v) (.inl 0) = v (.inl 0) := by
  simp [rankTwoCoordinateChange,Matrix.fromBlocks_mulVec,rankTwoTail,
    Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

theorem regularFourChange_pivot (v : Fin 2 ⊕ Fin 2 → R) :
    (regularFourChange *ᵥ v) (.inl 0) = v (.inl 0) := by
  simp [regularFourChange,Matrix.fromBlocks_mulVec,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

def rankTwoJordanConstantChange (c : K) (w : n → K) :
    Matrix ((Fin 2 ⊕ n) ⊕ (Fin 2 ⊕ n))
      ((Fin 2 ⊕ Fin 2) ⊕ ((Fin 1 ⊕ Fin 1) × n)) K :=
  (pairedCoordinateChange (rankTwoCoordinateChange c w) (rankTwoCoordinateInverse c w)).submatrix
    id (rankTwoRegularIndex n) *
    Matrix.fromBlocks regularFourChange 0 0 (1 : Matrix ((Fin 1 ⊕ Fin 1) × n) ((Fin 1 ⊕ Fin 1) × n) K)

theorem rankTwoJordanConstantChange_pivot (c : K) (w : n → K)
    (v : ((Fin 2 ⊕ Fin 2) ⊕ ((Fin 1 ⊕ Fin 1) × n)) → K) :
    (rankTwoJordanConstantChange c w *ᵥ v) (.inl (.inl 0)) = v (.inl (.inl 0)) := by
  rw [rankTwoJordanConstantChange,← Matrix.mulVec_mulVec,Matrix.submatrix_mulVec_equiv]
  simp only [Function.comp_apply,id_eq,pairedCoordinateChange,Matrix.fromBlocks_mulVec,
    Matrix.zero_mulVec,add_zero,Sum.elim_inl]
  rw [rankTwoCoordinateChange_pivot]
  simp [rankTwoRegularIndex,regularFourChange_pivot]

end FD56
