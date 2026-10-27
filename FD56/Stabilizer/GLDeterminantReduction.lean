/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GLKirillovEntries
import FD56.LinearAlgebra.HyperbolicSchurDeterminant

/-! Removing a full row block reduces the GL Kirillov determinant to a smaller pair. -/

noncomputable section
namespace FD56
open Matrix

def glRowReductionIndex (m r : Type*) :
    ((m × (m ⊕ r)) ⊕ (m × (m ⊕ r))) ⊕ SLInput r m ≃ SLInput (m ⊕ r) m where
  toFun
    | .inl (.inl (i,j)) => .inl (.inl i,j)
    | .inl (.inr (i,j)) => .inr (j,i)
    | .inr (.inl (i,j)) => .inl (.inr i,.inr j)
    | .inr (.inr (i,j)) => .inl (.inr i,.inl j)
  invFun
    | .inl (.inl i,j) => .inl (.inl (i,j))
    | .inl (.inr i,.inr j) => .inr (.inl (i,j))
    | .inl (.inr i,.inl j) => .inr (.inr (i,j))
    | .inr (j,i) => .inl (.inr (i,j))
  left_inv v := by rcases v with (⟨i,j⟩|⟨i,j⟩)|(⟨i,j⟩|⟨i,j⟩) <;> rfl
  right_inv v := by rcases v with ⟨i|i,j|j⟩|⟨j,i⟩ <;> rfl

def glTopRowIndex (m r : Type*) : m × (m ⊕ r) → SLInput (m ⊕ r) m :=
  fun (i,j) => .inl (.inl i,j)

def glReducedStateIndex (m r : Type*) : SLInput r m → SLInput (m ⊕ r) m
  | .inl (i,j) => .inl (.inr i,.inr j)
  | .inr (i,j) => .inl (.inr i,.inl j)

variable {R m r : Type*} [CommRing R] [Fintype m] [Fintype r]
  [DecidableEq m] [DecidableEq r]

theorem glKirillovMatrix_row_reduction_blocks (A : Matrix m m R) (B : Matrix m r R)
    (C : Matrix r m R) (D : Matrix r r R) :
    let H := glKirillovMatrix (Matrix.fromBlocks A B C D) (Matrix.fromCols (1 : Matrix m m R) 0)
    H.submatrix (glRowReductionIndex m r) (glRowReductionIndex m r)=
      Matrix.fromBlocks (hyperbolicCorner (H.submatrix (glTopRowIndex m r) (glTopRowIndex m r)))
        (Matrix.fromRows (H.submatrix (glTopRowIndex m r) (glReducedStateIndex m r)) 0)
        (Matrix.fromCols (H.submatrix (glReducedStateIndex m r) (glTopRowIndex m r)) 0)
        (glKirillovMatrix D B) := by
  intro H
  funext u v
  rcases u with (⟨i,j⟩|⟨i,j⟩)|(⟨i,j⟩|⟨i,j⟩) <;>
    rcases v with (⟨a,b⟩|⟨a,b⟩)|(⟨a,b⟩|⟨a,b⟩)
  all_goals try rfl
  all_goals simp [H,glRowReductionIndex,glTopRowIndex,glReducedStateIndex,hyperbolicCorner,
    glKirillovMatrix_state_state,glKirillovMatrix_state_translation,
    glKirillovMatrix_translation_state,glKirillovMatrix_translation_translation,
    Matrix.one_apply]
  all_goals split_ifs <;> simp_all [Prod.mk.injEq,eq_comm]

theorem glKirillovMatrix_row_reduction_det (A : Matrix m m R) (B : Matrix m r R)
    (C : Matrix r m R) (D : Matrix r r R) :
    (glKirillovMatrix (Matrix.fromBlocks A B C D) (Matrix.fromCols (1 : Matrix m m R) 0)).det=
      (glKirillovMatrix D B).det := by
  let H := glKirillovMatrix (Matrix.fromBlocks A B C D) (Matrix.fromCols (1 : Matrix m m R) 0)
  have h := congrArg Matrix.det (glKirillovMatrix_row_reduction_blocks A B C D)
  rw [Matrix.det_submatrix_equiv_self,hyperbolic_schur_det] at h
  exact h

end FD56
