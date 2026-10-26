/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.RankTwoTraceDecomposition

/-! An actual square GL pole decomposition with its trace functional retained. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

theorem congruence_row_reindex {R a b c : Type*} [CommRing R] [Fintype a] [Fintype c]
    (M : Matrix a b R) (A : Matrix c c R) (e : a ≃ c) :
    (M.submatrix e.symm id).transpose*A*M.submatrix e.symm id = M.transpose*A.submatrix e e*M := by
  have hA : A=(A.submatrix e e).submatrix e.symm e.symm := by ext i j; simp
  conv_lhs => rw [hA]
  change M.transpose.submatrix id e.symm*(A.submatrix e e).submatrix e.symm e.symm*
    M.submatrix e.symm id = _
  rw [Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv,Matrix.submatrix_id_id]

theorem congruence_column_reindex {R a b c : Type*} [CommRing R] [Fintype a]
    (M : Matrix a b R) (A : Matrix a a R) (e : c → b) :
    (M.submatrix id e).transpose*A*M.submatrix id e = (M.transpose*A*M).submatrix e e := by
  change M.transpose.submatrix e (Equiv.refl _) * A.submatrix (Equiv.refl _) (Equiv.refl _) *
    M.submatrix (Equiv.refl _) e = _
  rw [Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv]

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n] [LinearOrder (n × n)]

def squareGLPoleConstantChange (lam : n → K) (A B : Matrix n n K) :
    Matrix (SLInput n n) ((n ⊕ n) × n) K :=
  (squareGLPartnerSign (R := K) (n := n)).submatrix (squareGLPoleIndex n).symm id *
    (lowerBlockShift (regularPoleCorrection (fun i : n × n => lam i.2)
      (squareGLCommutatorBlock A) (squareGLCommutatorBlock B))).submatrix id (Equiv.sumProdDistrib n n n)

theorem squareGLPoleConstantChange_certificate (lam : n → K) (hlam : Function.Injective lam)
    (A B : Matrix n n K) :
    ∃ S : Matrix ((n ⊕ n) × n) (SLInput n n) K,
      squareGLPoleConstantChange lam A B*S=1 ∧ S*squareGLPoleConstantChange lam A B=1 ∧
      ((squareGLPoleConstantChange lam A B).map C).transpose *
          glKirillovMatrix (affineMatrixPencil A B) (Matrix.diagonal (fun i => X-C (lam i))) *
          (squareGLPoleConstantChange lam A B).map C =
        Matrix.blockDiagonal (fun i => pairedCoupling
          ((starCoupling i (fun j => -(A j i+lam i*B j i))).map C) (X-C (lam i))) := by
  let Z := regularPoleCorrection (fun i : n × n => lam i.2)
    (squareGLCommutatorBlock A) (squareGLCommutatorBlock B)
  let e := squareGLPoleIndex n
  let f := Equiv.sumProdDistrib n n n
  let Q := squareGLPartnerSign (R := K) (n := n)
  let G := Q.submatrix e.symm id
  let H := Q.submatrix id e.symm
  let U := (lowerBlockShift Z).submatrix id f
  let V := (lowerBlockShift (-Z)).submatrix f id
  have hGH : G*H=1 := by
    change Q.submatrix e.symm (Equiv.refl _) * Q.submatrix (Equiv.refl _) e.symm = 1
    rw [Matrix.submatrix_mul_equiv,squareGLPartnerSign_inverse]
    exact Matrix.submatrix_one_equiv e.symm
  have hHG : H*G=1 := by
    dsimp [H,G]
    rw [Matrix.submatrix_mul_equiv,squareGLPartnerSign_inverse,Matrix.submatrix_id_id]
  have hUV : U*V=1 := by
    dsimp [U,V]
    rw [Matrix.submatrix_mul_equiv,lowerBlockShift_inverse,Matrix.submatrix_id_id]
  have hVU : V*U=1 := by
    change (lowerBlockShift (-Z)).submatrix f (Equiv.refl _) *
      (lowerBlockShift Z).submatrix (Equiv.refl _) f = 1
    rw [Matrix.submatrix_mul_equiv]
    have h := lowerBlockShift_inverse (-Z)
    simp only [neg_neg] at h
    rw [h]
    exact Matrix.submatrix_one_equiv f
  have hG : (G.map C).transpose *
      glKirillovMatrix (affineMatrixPencil A B) (Matrix.diagonal (fun i => X-C (lam i))) * G.map C =
      regularPolePencil (fun i : n × n => lam i.2)
        (squareGLCommutatorBlock A) (squareGLCommutatorBlock B) := by
    change ((Q.map C).submatrix e.symm id).transpose * _ * (Q.map C).submatrix e.symm id = _
    rw [congruence_row_reindex,glKirillovMatrix_diagonal_reindex,
      squareGLPartnerSign_map,squareGLPartnerSign_congruence,squareGLCommutatorBlock_affine]
    rfl
  have hU : (U.map C).transpose *
      regularPolePencil (fun i : n × n => lam i.2)
        (squareGLCommutatorBlock A) (squareGLCommutatorBlock B) * U.map C =
      Matrix.blockDiagonal (regularLocalPolePencil lam (squareGLCommutatorBlock A) (squareGLCommutatorBlock B)) := by
    change (((lowerBlockShift Z).map C).submatrix id f).transpose * _ *
      ((lowerBlockShift Z).map C).submatrix id f = _
    rw [congruence_column_reindex,lowerBlockShift_map]
    unfold regularPolePencil
    rw [lowerBlockShift_congruence,regularPoleCorrection_polynomial _ _ _
      (squareGLCommutatorBlock_skew A) (squareGLCommutatorBlock_skew B)
      (squareGLCommutatorBlock_diag_zero B)]
    exact separated_poles_reindex lam hlam (squareGLCommutatorBlock A) (squareGLCommutatorBlock B)
  have hlocal : regularLocalPolePencil lam (squareGLCommutatorBlock A) (squareGLCommutatorBlock B) =
      fun i => pairedCoupling ((starCoupling i (fun j => -(A j i+lam i*B j i))).map C) (X-C (lam i)) := by
    funext i
    simp only [regularLocalPolePencil,squareGL_resonant_coupling,pairedCoupling]
  refine ⟨V*H,?_,?_,?_⟩
  · change (G*U)*(V*H)=1
    rw [Matrix.mul_assoc,← Matrix.mul_assoc U,hUV,Matrix.one_mul,hGH]
  · change (V*H)*(G*U)=1
    rw [Matrix.mul_assoc,← Matrix.mul_assoc H,hHG,Matrix.one_mul,hVU]
  · change ((G*U).map C).transpose * _ * (G*U).map C = _
    rw [Matrix.map_mul,Matrix.transpose_mul]
    calc
      _ = (U.map C).transpose * ((G.map C).transpose *
          glKirillovMatrix (affineMatrixPencil A B) (Matrix.diagonal (fun i => X-C (lam i))) * G.map C) * U.map C := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hG,hU,hlocal]

theorem squareGLPoleConstantChange_trace (lam : n → K) (A B : Matrix n n K)
    (v : ((n ⊕ n) × n) → K) :
    Matrix.trace (matrixPairEquiv K K n n (squareGLPoleConstantChange lam A B *ᵥ v)).1 =
      ∑ i, v (.inl i,i) := squareGL_pole_trace_coordinate _ _

end FD56
