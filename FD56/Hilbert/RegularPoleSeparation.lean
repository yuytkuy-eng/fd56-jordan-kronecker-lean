/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.RegularPoleCorrection
import FD56.Stabilizer.GenericRows

/-! A constant invertible congruence separates all unequal regular poles. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

def lowerBlockShift (Z : Matrix n n R) : Matrix (n ⊕ n) (n ⊕ n) R :=
  Matrix.fromBlocks 1 0 Z 1

theorem lowerBlockShift_inverse (Z : Matrix n n R) :
    lowerBlockShift Z * lowerBlockShift (-Z) = 1 := by
  simp [lowerBlockShift,Matrix.fromBlocks_multiply,Matrix.fromBlocks_one]

theorem lowerBlockShift_congruence (A D Z : Matrix n n R) :
    (lowerBlockShift Z).transpose * Matrix.fromBlocks A D (-D) 0 * lowerBlockShift Z =
      Matrix.fromBlocks (A+D*Z-Z.transpose*D) D (-D) 0 := by
  simp only [lowerBlockShift,Matrix.fromBlocks_transpose,Matrix.transpose_one,
    Matrix.transpose_zero,Matrix.fromBlocks_multiply,Matrix.mul_zero,Matrix.zero_mul,
    Matrix.one_mul,Matrix.mul_one,zero_add,add_zero,Matrix.mul_neg]
  abel

omit [Fintype n] in
theorem lowerBlockShift_map {S : Type*} [CommRing S] (f : R →+* S)
    (Z : Matrix n n R) : (lowerBlockShift Z).map f = lowerBlockShift (Z.map f) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [lowerBlockShift,Matrix.one_apply]

variable {K : Type*} [Field K] [LinearOrder n]

def regularPoleDiagonal (lam : n → K) : Matrix n n K[X] :=
  Matrix.diagonal (fun i => X-C (lam i))

def regularPolePencil (lam : n → K) (A B : Matrix n n K) :
    Matrix (n ⊕ n) (n ⊕ n) K[X] :=
  Matrix.fromBlocks (affineMatrixPencil A B) (regularPoleDiagonal lam)
    (-(regularPoleDiagonal lam)) 0

theorem regularPoleCorrection_polynomial (lam : n → K) (A B : Matrix n n K)
    (hA : A.transpose = -A) (hB : B.transpose = -B) (hBd : ∀ i, B i i=0) :
    affineMatrixPencil A B + regularPoleDiagonal lam * (regularPoleCorrection lam A B).map C -
      ((regularPoleCorrection lam A B).map C).transpose * regularPoleDiagonal lam =
        (regularPoleResidual lam A B).map C := by
  funext i j
  simp only [Matrix.sub_apply,Matrix.add_apply,regularPoleDiagonal,Matrix.diagonal_mul,
    Matrix.mul_diagonal,Matrix.map_apply,Matrix.transpose_apply,affineMatrixPencil]
  obtain ⟨hlin,hconst⟩ := regularPoleCorrection_entries lam A B hA hB hBd i j
  calc
    _ = C (A i j-lam i*regularPoleCorrection lam A B i j+
        lam j*regularPoleCorrection lam A B j i) +
        X*C (B i j+regularPoleCorrection lam A B i j-regularPoleCorrection lam A B j i) := by
      simp only [map_add,map_sub,map_mul]
      ring
    _ = _ := by simp only [hlin,hconst,map_zero,mul_zero,add_zero]

theorem regular_pole_constant_separation (lam : n → K) (A B : Matrix n n K)
    (hA : A.transpose = -A) (hB : B.transpose = -B) (hBd : ∀ i, B i i=0) :
    ∃ T S : Matrix (n ⊕ n) (n ⊕ n) K,
      T*S=1 ∧ S*T=1 ∧
      (T.map C).transpose * regularPolePencil lam A B * T.map C =
        Matrix.fromBlocks ((regularPoleResidual lam A B).map C) (regularPoleDiagonal lam)
          (-(regularPoleDiagonal lam)) 0 := by
  let Z := regularPoleCorrection lam A B
  refine ⟨lowerBlockShift Z,lowerBlockShift (-Z),lowerBlockShift_inverse Z,?_,?_⟩
  · simpa only [neg_neg] using lowerBlockShift_inverse (-Z)
  · rw [lowerBlockShift_map]
    change (lowerBlockShift (Z.map C)).transpose *
      Matrix.fromBlocks (affineMatrixPencil A B) (regularPoleDiagonal lam)
        (-(regularPoleDiagonal lam)) 0 * lowerBlockShift (Z.map C) = _
    rw [lowerBlockShift_congruence,regularPoleCorrection_polynomial lam A B hA hB hBd]

end FD56
