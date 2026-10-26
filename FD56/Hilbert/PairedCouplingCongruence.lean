/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.RankTwoCouplingNormalization
import FD56.Hilbert.RegularJordanBlock

/-! A coordinate change and its dual preserve the scalar pairing in a pencil. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

def pairedCoupling (A : Matrix n n R) (t : R) : Matrix (n ⊕ n) (n ⊕ n) R :=
  Matrix.fromBlocks A (t • (1 : Matrix n n R)) (-(t • (1 : Matrix n n R))) 0

def pairedCoordinateChange (Q S : Matrix n n R) : Matrix (n ⊕ n) (n ⊕ n) R :=
  Matrix.fromBlocks Q 0 0 S.transpose

theorem pairedCoordinateChange_inverse (Q S : Matrix n n R) (hQS : Q*S=1) :
    pairedCoordinateChange Q S * pairedCoordinateChange S Q = 1 := by
  simp only [pairedCoordinateChange, Matrix.fromBlocks_multiply, Matrix.mul_zero,
    Matrix.zero_mul, zero_add, add_zero, ← Matrix.transpose_mul, hQS,
    Matrix.transpose_one, Matrix.fromBlocks_one]

theorem pairedCoordinateChange_congruence (Q S A : Matrix n n R) (hSQ : S*Q=1)
    (t : R) :
    (pairedCoordinateChange Q S).transpose * pairedCoupling A t * pairedCoordinateChange Q S =
      pairedCoupling (Q.transpose*A*Q) t := by
  simp only [pairedCoordinateChange, pairedCoupling, Matrix.fromBlocks_transpose,
    Matrix.transpose_zero, Matrix.transpose_transpose, Matrix.fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg,
    Matrix.neg_mul, ← Matrix.transpose_mul, hSQ, Matrix.transpose_one, smul_zero, neg_zero]

omit [Fintype n] [DecidableEq n] in
theorem pairedCoordinateChange_map {S : Type*} [CommRing S] (f : R →+* S)
    (Q T : Matrix n n R) :
    (pairedCoordinateChange Q T).map f = pairedCoordinateChange (Q.map f) (T.map f) := by
  ext i j
  cases i <;> cases j <;> simp [pairedCoordinateChange]

variable {K : Type*} [Field K]

theorem pairedCoupling_constant_normalization (A Q S A' : Matrix n n K)
    (hQS : Q*S=1) (hSQ : S*Q=1) (hA : Q.transpose*A*Q=A') (a : K) :
    ∃ T U : Matrix (n ⊕ n) (n ⊕ n) K,
      T*U=1 ∧ U*T=1 ∧
      (T.map C).transpose * pairedCoupling (A.map C) (X-C a) * T.map C =
        pairedCoupling (A'.map C) (X-C a) := by
  refine ⟨pairedCoordinateChange Q S, pairedCoordinateChange S Q,
    pairedCoordinateChange_inverse Q S hQS,
    pairedCoordinateChange_inverse S Q hSQ, ?_⟩
  have hSQ' : S.map C * Q.map C = (1 : Matrix n n K[X]) := by
    rw [← Matrix.map_mul, hSQ, Matrix.map_one _ (map_zero C) (map_one C)]
  rw [pairedCoordinateChange_map, pairedCoordinateChange_congruence _ _ _ hSQ']
  have hA' : (Q.map C).transpose * A.map C * Q.map C = A'.map C := by
    change Q.transpose.map C * A.map C * Q.map C = _
    rw [← Matrix.map_mul, ← Matrix.map_mul, hA]
  rw [hA']

end FD56
