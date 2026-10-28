/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PolynomialDeterminantDerivative
import FD56.Stabilizer.GenericRows

/-! Finite directional determinant identities, including a triangular
completion identity with no invertibility assumption on the terminal block. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {R n m : Type*} [CommRing R]
  [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

def matrixDetDifferential (A E : Matrix n n R) : R := Matrix.trace (A.adjugate*E)

theorem matrixDetDifferential_mul_right (A E H : Matrix n n R) :
    matrixDetDifferential (A*H) (E*H)=H.det*matrixDetDifferential A E := by
  dsimp only [matrixDetDifferential]
  rw [Matrix.adjugate_mul_distrib]
  calc
    Matrix.trace (H.adjugate*A.adjugate*(E*H))=
        Matrix.trace (H*H.adjugate*(A.adjugate*E)) := by
      rw [← Matrix.mul_assoc (H.adjugate*A.adjugate) E H,Matrix.trace_mul_comm _ H]
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [Matrix.mul_adjugate,Matrix.smul_mul,Matrix.one_mul,Matrix.trace_smul,smul_eq_mul]

theorem matrixDetDifferential_reindex (e : m ≃ n) (A E : Matrix n n R) :
    matrixDetDifferential (A.submatrix e e) (E.submatrix e e)=matrixDetDifferential A E := by
  dsimp only [matrixDetDifferential]
  rw [Matrix.adjugate_submatrix_equiv_self,Matrix.submatrix_mul_equiv]
  exact Equiv.sum_comp e (fun i => (A.adjugate*E) i i)

theorem matrixDetDifferential_eq_eval_derivative (A E : Matrix n n R) :
    matrixDetDifferential A E=(Polynomial.evalRingHom (0:R))
      (Polynomial.derivative (affineMatrixPencil A E).det) := by
  rw [polynomial_det_derivative,AddMonoidHom.map_trace]
  change _=Matrix.trace (((affineMatrixPencil A E).adjugate*
    (affineMatrixPencil A E).map Polynomial.derivative).map (Polynomial.evalRingHom (0:R)))
  rw [Matrix.map_mul]
  have hmap : (affineMatrixPencil A E).map (Polynomial.evalRingHom (0:R))=A := by
    funext i j
    simp [affineMatrixPencil]
  have hderiv : ((affineMatrixPencil A E).map Polynomial.derivative).map
      (Polynomial.evalRingHom (0:R))=E := by
    funext i j
    simp [affineMatrixPencil]
  rw [hderiv,← RingHom.mapMatrix_apply,(Polynomial.evalRingHom (0:R)).map_adjugate,
    RingHom.mapMatrix_apply,hmap]
  rfl

theorem matrixDetDifferential_triangular
    (B : Matrix n n R) (C E : Matrix m n R) (D F : Matrix m m R) :
    matrixDetDifferential (Matrix.fromBlocks 1 0 C D)
      (Matrix.fromBlocks B 0 E F)=Matrix.trace B*D.det+matrixDetDifferential D F := by
  rw [matrixDetDifferential_eq_eval_derivative]
  have hp : affineMatrixPencil (Matrix.fromBlocks 1 0 C D) (Matrix.fromBlocks B 0 E F)=
      Matrix.fromBlocks (affineMatrixPencil 1 B) 0 (affineMatrixPencil C E)
        (affineMatrixPencil D F) := by
    funext i j
    rcases i with i|i <;> rcases j with j|j <;> simp [affineMatrixPencil]
  rw [hp,Matrix.det_fromBlocks_zero₁₂,Polynomial.derivative_mul,map_add,map_mul,map_mul,
    ← matrixDetDifferential_eq_eval_derivative,← matrixDetDifferential_eq_eval_derivative]
  have hdet (U V : Matrix m m R) :
      (Polynomial.evalRingHom (0:R)) (affineMatrixPencil U V).det=U.det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
    congr 1
    funext i j
    simp [affineMatrixPencil]
  rw [hdet]
  have hone : (Polynomial.evalRingHom (0:R)) (affineMatrixPencil (1:Matrix n n R) B).det=1 := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
    have he : (affineMatrixPencil (1:Matrix n n R) B).map (Polynomial.evalRingHom (0:R))=1 := by
      funext i j
      simp [affineMatrixPencil]
    rw [he,Matrix.det_one]
  rw [hone,one_mul]
  simp [matrixDetDifferential]

end FD56
