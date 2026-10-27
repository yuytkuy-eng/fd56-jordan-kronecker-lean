/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GLKirillovPencil

/-! Entry formulas for the actual GL Kirillov matrix. -/

noncomputable section
namespace FD56
open Matrix

variable {R n m : Type*} [CommRing R] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem glKirillovMatrix_state_state (M : Matrix n n R) (P : Matrix m n R) (i j a b : n) :
    glKirillovMatrix M P (.inl (i,j)) (.inl (a,b))=
      (if b=i then M j a else 0)-(if a=j then M b i else 0) := by
  by_cases hbi : b=i <;> by_cases haj : a=j
  all_goals simp [glKirillovMatrix,glTraceDualIndexEquiv,glEquationMatrix,LinearMap.toMatrix'_apply,
    glEquationLinearMap,matrixPairEquiv,stabilizerResidual,Matrix.mul_apply,Pi.single_apply]
  all_goals simp_all [eq_comm]

theorem glKirillovMatrix_state_translation (M : Matrix n n R) (P : Matrix m n R)
    (i j a : n) (b : m) :
    glKirillovMatrix M P (.inl (i,j)) (.inr (a,b))=-(if a=j then P b i else 0) := by
  by_cases haj : a=j
  all_goals simp [glKirillovMatrix,glTraceDualIndexEquiv,glEquationMatrix,LinearMap.toMatrix'_apply,
    glEquationLinearMap,matrixPairEquiv,stabilizerResidual,Matrix.mul_apply,Pi.single_apply,haj,eq_comm]

theorem glKirillovMatrix_translation_state (M : Matrix n n R) (P : Matrix m n R)
    (i a b : n) (j : m) :
    glKirillovMatrix M P (.inr (i,j)) (.inl (a,b))=if b=i then P j a else 0 := by
  by_cases hbi : b=i
  all_goals simp [glKirillovMatrix,glTraceDualIndexEquiv,glEquationMatrix,LinearMap.toMatrix'_apply,
    glEquationLinearMap,matrixPairEquiv,stabilizerResidual,Matrix.mul_apply,Pi.single_apply,hbi,eq_comm]

theorem glKirillovMatrix_translation_translation (M : Matrix n n R) (P : Matrix m n R)
    (i a : n) (j b : m) : glKirillovMatrix M P (.inr (i,j)) (.inr (a,b))=0 := by
  simp [glKirillovMatrix,glTraceDualIndexEquiv,glEquationMatrix,LinearMap.toMatrix'_apply,
    glEquationLinearMap,matrixPairEquiv,stabilizerResidual,Matrix.mul_apply,Pi.single_apply]

end FD56
