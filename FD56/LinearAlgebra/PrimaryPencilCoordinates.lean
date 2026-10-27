/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.MatrixPrimaryRestriction
import FD56.LinearAlgebra.PolynomialPencilPrimaryData

/-! The actual restricted pencil in coordinates of a primary-space basis. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K n i : Type*} [Field K] [Fintype n] [DecidableEq n]
  [Fintype i] [DecidableEq i]

def subspaceBasisColumns (U : Submodule K (n → K)) (b : Basis i K U) : Matrix n i K :=
  fun r j => (b j).val r

theorem subspace_basis_bilinear_matrix (B : Matrix n n K)
    (U : Submodule K (n → K)) (b : Basis i K U) :
    BilinForm.toMatrix b (B.toBilin'.restrict U)=
      (subspaceBasisColumns U b).transpose*B*subspaceBasisColumns U b := by
  ext j k
  rw [BilinForm.toMatrix_apply]
  change B.toBilin' (b j).val (b k).val=_
  rw [Matrix.toBilin'_apply']
  symm
  change (((subspaceBasisColumns U b).transpose*B) *ᵥ (b k).val) j=_
  rw [← Matrix.mulVec_mulVec]
  rfl

theorem primary_shift_form_identity (A B : Matrix n n K) (hd : B.det≠0) (a : K) :
    let f : Module.End K (n → K) := Matrix.toLin' (-B⁻¹*A)
    (B.toBilin'.restrict (f.maxGenEigenspace a)).compRight (primaryShift f a)=
      -(A.toBilin'.restrict (f.maxGenEigenspace a))-
        a•(B.toBilin'.restrict (f.maxGenEigenspace a)) := by
  dsimp only
  have hBA : B*(-B⁻¹*A) = -A := by
    rw [← Matrix.mul_assoc,Matrix.mul_neg,Matrix.mul_nonsing_inv B (isUnit_iff_ne_zero.mpr hd),
      Matrix.neg_mul,Matrix.one_mul]
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change B.toBilin' x.val ((Matrix.toLin' (-B⁻¹*A)-algebraMap K _ a) y.val)=
    -A.toBilin' x.val y.val-a*B.toBilin' x.val y.val
  simp only [LinearMap.sub_apply,Module.algebraMap_end_apply,map_sub,map_smul,smul_eq_mul,
    Matrix.toBilin'_apply',Matrix.toLin'_apply,Matrix.mulVec_mulVec,hBA,
    Matrix.neg_mulVec,dotProduct_neg]

theorem affine_pencil_rectangular_congruence (A B : Matrix n n K) (Q : Matrix n i K) :
    (Q.map C).transpose*affineMatrixPencil A B*Q.map C=
      affineMatrixPencil (Q.transpose*A*Q) (Q.transpose*B*Q) := by
  have hp : affineMatrixPencil A B=A.map C+(X : K[X])•B.map C := by
    funext r s
    simp only [affineMatrixPencil,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Matrix.map_apply]
  have hq : affineMatrixPencil (Q.transpose*A*Q) (Q.transpose*B*Q)=
      (Q.transpose*A*Q).map C+(X : K[X])•(Q.transpose*B*Q).map C := by
    funext r s
    simp only [affineMatrixPencil,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Matrix.map_apply]
  rw [hp,hq,Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul]
  simp only [Matrix.map_mul,Matrix.transpose_map]

theorem primary_affine_pencil_coordinates (A B : Matrix n n K) (hd : B.det≠0) (a : K)
    (b : Basis i K (Module.End.maxGenEigenspace (Matrix.toLin' (-B⁻¹*A)) a)) :
    let f : Module.End K (n → K) := Matrix.toLin' (-B⁻¹*A)
    let Q := subspaceBasisColumns (f.maxGenEigenspace a) b
    let G : Matrix i i K := BilinForm.toMatrix b (B.toBilin'.restrict (f.maxGenEigenspace a))
    let N : Matrix i i K := LinearMap.toMatrix b b (primaryShift f a)
    (Q.map C).transpose*affineMatrixPencil A B*Q.map C=
      (X-C a)•G.map C-(G*N).map C := by
  dsimp only
  let f : Module.End K (n → K) := Matrix.toLin' (-B⁻¹*A)
  let U := f.maxGenEigenspace a
  let Q := subspaceBasisColumns U b
  let G := BilinForm.toMatrix b (B.toBilin'.restrict U)
  let N := LinearMap.toMatrix b b (primaryShift f a)
  have hG : G=Q.transpose*B*Q := subspace_basis_bilinear_matrix B U b
  have hN : G*N=-(Q.transpose*A*Q)-a•G := by
    change BilinForm.toMatrix b (B.toBilin'.restrict U)*LinearMap.toMatrix b b (primaryShift f a)=_
    rw [← BilinForm.toMatrix_compRight,primary_shift_form_identity A B hd a]
    funext r s
    rw [BilinForm.toMatrix_apply]
    change -A.toBilin' (b r).val (b s).val-a*B.toBilin' (b r).val (b s).val=
      -(Q.transpose*A*Q) r s-a*G r s
    have he := congrFun (congrFun (subspace_basis_bilinear_matrix A U b) r) s
    rw [BilinForm.toMatrix_apply] at he
    change A.toBilin' (b r).val (b s).val=(Q.transpose*A*Q) r s at he
    rw [he]
    dsimp only [G]
    rw [BilinForm.toMatrix_apply]
    rfl
  change (Q.map C).transpose*affineMatrixPencil A B*Q.map C=(X-C a)•G.map C-(G*N).map C
  rw [affine_pencil_rectangular_congruence,← hG,hN]
  funext r s
  simp [affineMatrixPencil,Matrix.map_apply]
  ring

end FD56
