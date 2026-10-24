/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Data.Fin.VecNotation

/-! Evaluation rules for the finite matrices used in the explicit witnesses. -/

namespace FD56

theorem matrix_cons_five {α : Type*} {m : ℕ} (x : α) (u : Fin (m+5) → α) :
    Matrix.vecCons x u (5 : Fin (m+6))=u 4 := rfl

theorem matrix_cons_six {α : Type*} {m : ℕ} (x : α) (u : Fin (m+6) → α) :
    Matrix.vecCons x u (6 : Fin (m+7))=u 5 := rfl

theorem matrix_cons_seven {α : Type*} {m : ℕ} (x : α) (u : Fin (m+7) → α) :
    Matrix.vecCons x u (7 : Fin (m+8))=u 6 := rfl

theorem matrix_cons_eight {α : Type*} {m : ℕ} (x : α) (u : Fin (m+8) → α) :
    Matrix.vecCons x u (8 : Fin (m+9))=u 7 := rfl

theorem matrix_cons_nine {α : Type*} {m : ℕ} (x : α) (u : Fin (m+9) → α) :
    Matrix.vecCons x u (9 : Fin (m+10))=u 8 := rfl

end FD56
