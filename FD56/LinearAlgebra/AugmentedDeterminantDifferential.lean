/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.MatrixDeterminantDifferential

/-! Splitting a full-row-rank prefix separates its determinant variation
from the variation of the terminal kernel coordinates. -/

noncomputable section
namespace FD56
open Matrix

variable {R a b k : Type*} [CommRing R]
  [Fintype a] [Fintype b] [Fintype k]
  [DecidableEq a] [DecidableEq b] [DecidableEq k]

theorem augmented_completion_determinant (e : b ≃ a ⊕ k)
    (A : Matrix a b R) (S : Matrix b a R) (V : Matrix b k R)
    (hAS : A*S=1) (hAV : A*V=0) (T : Matrix k b R) :
    ((Matrix.fromCols S V).submatrix id e).det *
      ((Matrix.fromRows A T).submatrix e id).det=(T*V).det := by
  rw [mul_comm,← Matrix.det_mul,
    ← Matrix.submatrix_mul (Matrix.fromRows A T) (Matrix.fromCols S V) e id e Function.bijective_id,
    Matrix.det_submatrix_equiv_self,Matrix.fromRows_mul_fromCols,hAS,hAV,
    Matrix.det_fromBlocks_zero₁₂,Matrix.det_one,one_mul]

theorem augmented_completion_differential (e : b ≃ a ⊕ k)
    (A : Matrix a b R) (S : Matrix b a R) (V : Matrix b k R)
    (hAS : A*S=1) (hAV : A*V=0)
    (B : Matrix a a R) (T U : Matrix k b R) :
    ((Matrix.fromCols S V).submatrix id e).det *
      matrixDetDifferential ((Matrix.fromRows A T).submatrix e id)
        ((Matrix.fromRows (B*A) U).submatrix e id)=
      Matrix.trace B*(T*V).det+matrixDetDifferential (T*V) (U*V) := by
  rw [← matrixDetDifferential_mul_right,
    ← Matrix.submatrix_mul (Matrix.fromRows A T) (Matrix.fromCols S V) e id e Function.bijective_id,
    ← Matrix.submatrix_mul (Matrix.fromRows (B*A) U) (Matrix.fromCols S V) e id e Function.bijective_id,
    matrixDetDifferential_reindex,Matrix.fromRows_mul_fromCols,Matrix.fromRows_mul_fromCols,
    hAS,hAV,Matrix.mul_assoc,Matrix.mul_assoc,hAS,hAV,Matrix.mul_one,Matrix.mul_zero]
  exact matrixDetDifferential_triangular B (T*S) (U*S) (T*V) (U*V)

end FD56
