/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GLKirillovPencil
import Mathlib.Data.Matrix.Kronecker
import Mathlib.Algebra.GroupWithZero.Associated

/-! The square GL determinant is the row determinant raised to twice the state
dimension. This does not classify its regular blocks. -/

noncomputable section
namespace FD56
open Matrix
open scoped Kronecker

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

theorem glEquationMatrix_square_blocks (M P : Matrix n n R) :
    glEquationMatrix M P = Matrix.fromBlocks
      (P ⊗ₖ (1 : Matrix n n R)) 0
      ((glEquationMatrix M P).submatrix Sum.inr Sum.inl)
      (-((1 : Matrix n n R) ⊗ₖ P.transpose)) := by
  ext x y
  rcases x with ⟨i,j⟩ | ⟨i,j⟩ <;> rcases y with ⟨a,b⟩ | ⟨a,b⟩
  all_goals simp [glEquationMatrix, LinearMap.toMatrix'_apply, glEquationLinearMap,
    matrixPairEquiv, stabilizerResidual, Matrix.mul_apply, Matrix.kronecker_apply,
    Matrix.one_apply, Pi.single_apply, Matrix.submatrix_apply]
  all_goals by_cases h : i = a <;> by_cases h' : j = b <;> simp [h,h']

theorem glEquationMatrix_square_det (M P : Matrix n n R) :
    (glEquationMatrix M P).det =
      (-1 : R) ^ (Fintype.card n * Fintype.card n) * P.det ^ (2 * Fintype.card n) := by
  rw [glEquationMatrix_square_blocks, Matrix.det_fromBlocks_zero₁₂,
    Matrix.det_neg, Matrix.det_kronecker, Matrix.det_kronecker,
    Matrix.det_one, Matrix.det_transpose]
  simp only [one_pow, mul_one, one_mul, Fintype.card_prod]
  rw [mul_left_comm, ← pow_add]
  congr 2
  omega

private theorem sign_sum_swap (a : Type*) [Fintype a] [DecidableEq a] :
    Equiv.Perm.sign (Equiv.sumComm a a) = (-1 : ℤˣ) ^ Fintype.card a := by
  have hs : Equiv.Perm.sign (Equiv.sumComm a a) =
      Equiv.Perm.sign (Equiv.prodCongrLeft (fun _ : a => Equiv.swap false true)) := by
    apply Equiv.Perm.sign_eq_sign_of_equiv _ _ (Equiv.boolProdEquivSum a).symm
    intro x
    cases x <;> simp [Equiv.boolProdEquivSum, Equiv.prodCongrLeft_apply]
  rw [hs, Equiv.Perm.sign_prodCongrLeft]
  simp [Equiv.Perm.sign_swap]

theorem glTraceDualIndexEquiv_square_sign :
    Equiv.Perm.sign (glTraceDualIndexEquiv n n) =
      (-1 : ℤˣ) ^ (Fintype.card n * Fintype.card n) := by
  have he : glTraceDualIndexEquiv n n =
      (Equiv.sumCongr (Equiv.prodComm n n) (Equiv.prodComm n n)).trans
        (Equiv.sumComm (n × n) (n × n)) := by
    ext x
    cases x <;> rfl
  have hp : Equiv.Perm.sign (Equiv.prodComm n n) *
      Equiv.Perm.sign (Equiv.prodComm n n) = 1 := by
    rw [← Equiv.Perm.sign_trans]
    have h : (Equiv.prodComm n n).trans (Equiv.prodComm n n) = Equiv.refl (n × n) := by
      ext x <;> rfl
    rw [h, Equiv.Perm.sign_refl]
  rw [he, Equiv.Perm.sign_trans, Equiv.Perm.sign_sumCongr, hp, mul_one,
    sign_sum_swap, Fintype.card_prod]

theorem glKirillovMatrix_square_det (M P : Matrix n n R) :
    (glKirillovMatrix M P).det = P.det ^ (2 * Fintype.card n) := by
  rw [glKirillovMatrix, Matrix.det_permute, glEquationMatrix_square_det,
    glTraceDualIndexEquiv_square_sign]
  simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
    Int.cast_pow, Int.cast_neg, Int.cast_one]
  rw [← mul_assoc, ← mul_pow]
  simp

theorem glKirillovMatrix_square_det_associated (M P : Matrix n n R) :
    Associated (glKirillovMatrix M P).det (P.det ^ (2 * Fintype.card n)) := by
  rw [glKirillovMatrix, Matrix.det_permute, glEquationMatrix_square_det]
  have hs : IsUnit (↑(Equiv.Perm.sign (glTraceDualIndexEquiv n n)) : R) :=
    (Equiv.Perm.sign (glTraceDualIndexEquiv n n)).isUnit.map (Int.castRingHom R)
  have hn : IsUnit ((-1 : R) ^ (Fintype.card n * Fintype.card n)) :=
    (isUnit_one.neg).pow _
  rw [← mul_assoc]
  exact associated_unit_mul_left _ _ (hs.mul hn)

end FD56
