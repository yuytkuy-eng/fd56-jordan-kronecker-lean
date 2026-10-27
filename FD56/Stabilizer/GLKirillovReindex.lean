/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GLKirillovEntries

/-! Finite coordinate relabelling preserves the GL Kirillov determinant. -/

noncomputable section
namespace FD56
open Matrix

variable {R n m n' m' : Type*} [CommRing R]
  [Fintype n] [Fintype m] [Fintype n'] [Fintype m']
  [DecidableEq n] [DecidableEq m] [DecidableEq n'] [DecidableEq m']

theorem glKirillovMatrix_reindex (M : Matrix n n R) (P : Matrix m n R)
    (en : n' ≃ n) (em : m' ≃ m) :
    glKirillovMatrix (M.submatrix en en) (P.submatrix em en)=
      (glKirillovMatrix M P).submatrix
        (Equiv.sumCongr (en.prodCongr en) (en.prodCongr em))
        (Equiv.sumCongr (en.prodCongr en) (en.prodCongr em)) := by
  ext x y
  rcases x with ⟨i,j⟩|⟨i,j⟩ <;> rcases y with ⟨a,b⟩|⟨a,b⟩
  all_goals simp [glKirillovMatrix_state_state,glKirillovMatrix_state_translation,
    glKirillovMatrix_translation_state,glKirillovMatrix_translation_translation]

theorem glKirillovMatrix_det_reindex (M : Matrix n n R) (P : Matrix m n R)
    (en : n' ≃ n) (em : m' ≃ m) :
    (glKirillovMatrix (M.submatrix en en) (P.submatrix em en)).det=(glKirillovMatrix M P).det := by
  rw [glKirillovMatrix_reindex,Matrix.det_submatrix_equiv_self]

end FD56
