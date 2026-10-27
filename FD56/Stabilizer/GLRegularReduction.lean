/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GLDeterminantReduction

/-! A unimodular congruence separates the full-row-rank GL reduction.
For polynomial inputs the transformation is polynomial, and need not be constant. -/

noncomputable section
namespace FD56
open Matrix

variable {R a b : Type*} [CommRing R] [Fintype a] [Fintype b]
  [DecidableEq a] [DecidableEq b]

def hyperbolicSchurShift (B : Matrix a b R) : Matrix ((a ⊕ a) ⊕ b) ((a ⊕ a) ⊕ b) R :=
  Matrix.fromBlocks 1 (Matrix.fromRows 0 B) 0 1

theorem hyperbolicSchurShift_inverse (B : Matrix a b R) :
    hyperbolicSchurShift B*hyperbolicSchurShift (-B)=1 := by
  have hneg : Matrix.fromRows (0 : Matrix a b R) (-B)=-(Matrix.fromRows 0 B) := by
    ext (i|i) j <;> simp
  simp only [hyperbolicSchurShift,hneg,Matrix.fromBlocks_multiply,Matrix.mul_one,Matrix.one_mul,
    Matrix.mul_zero,Matrix.zero_mul,add_zero,zero_add,add_neg_cancel,neg_add_cancel,Matrix.fromBlocks_one]

theorem hyperbolicSchurShift_det (B : Matrix a b R) : (hyperbolicSchurShift B).det=1 := by
  simp [hyperbolicSchurShift,Matrix.det_fromBlocks_zero₂₁]

theorem hyperbolicSchurShift_congruence (A : Matrix a a R) (B : Matrix a b R) (D : Matrix b b R) :
    (hyperbolicSchurShift B).transpose *
        Matrix.fromBlocks (hyperbolicCorner A) (Matrix.fromRows B 0)
          (Matrix.fromCols (-B.transpose) 0) D * hyperbolicSchurShift B =
      Matrix.fromBlocks (hyperbolicCorner A) 0 0 D := by
  have hcol : Matrix.fromCols B.transpose (0 : Matrix b a R)+
      Matrix.fromCols (-B.transpose) 0=0 := by
    ext i (j|j) <;> simp
  have hrow : Matrix.fromRows (-B) (0 : Matrix a b R)+Matrix.fromRows B 0=0 := by
    ext (i|i) j <;> simp
  simp only [hyperbolicSchurShift,Matrix.fromBlocks_transpose,Matrix.transpose_zero,
    Matrix.transpose_one,Matrix.transpose_fromRows,hyperbolicCorner,Matrix.fromBlocks_multiply,
    Matrix.mul_zero,Matrix.zero_mul,Matrix.mul_one,Matrix.one_mul,zero_add,add_zero,
    Matrix.fromCols_mul_fromBlocks,Matrix.fromBlocks_mul_fromRows,Matrix.fromCols_mul_fromRows,
    Matrix.mul_neg,Matrix.neg_mul,Matrix.mul_zero,Matrix.zero_mul,Matrix.mul_one,Matrix.one_mul,
    zero_add,add_zero,neg_zero,hcol,hrow,Matrix.zero_mul,zero_add]

variable {m r : Type*} [Fintype m] [Fintype r] [DecidableEq m] [DecidableEq r]

theorem glKirillovMatrix_row_reduction_unimodular (A : Matrix m m R) (B : Matrix m r R)
    (C : Matrix r m R) (D : Matrix r r R) :
    let H := glKirillovMatrix (Matrix.fromBlocks A B C D) (Matrix.fromCols (1 : Matrix m m R) 0)
    let e := glRowReductionIndex m r
    ∃ T S : Matrix (((m × (m ⊕ r)) ⊕ (m × (m ⊕ r))) ⊕ SLInput r m)
      (((m × (m ⊕ r)) ⊕ (m × (m ⊕ r))) ⊕ SLInput r m) R,
      T*S=1 ∧ S*T=1 ∧ T.det=1 ∧
      T.transpose*H.submatrix e e*T=
        Matrix.fromBlocks (hyperbolicCorner (H.submatrix (glTopRowIndex m r) (glTopRowIndex m r)))
          0 0 (glKirillovMatrix D B) := by
  intro H e
  let J := H.submatrix (glTopRowIndex m r) (glReducedStateIndex m r)
  have hcross : H.submatrix (glReducedStateIndex m r) (glTopRowIndex m r)=-J.transpose := by
    ext i j
    exact congrFun (congrFun (glKirillovMatrix_skew (Matrix.fromBlocks A B C D)
      (Matrix.fromCols (1 : Matrix m m R) 0)) (glTopRowIndex m r j)) (glReducedStateIndex m r i)
  refine ⟨hyperbolicSchurShift J,hyperbolicSchurShift (-J),hyperbolicSchurShift_inverse J,
    ?_,hyperbolicSchurShift_det J,?_⟩
  · simpa only [neg_neg] using hyperbolicSchurShift_inverse (-J)
  · rw [glKirillovMatrix_row_reduction_blocks,hcross]
    exact hyperbolicSchurShift_congruence _ J _

end FD56
