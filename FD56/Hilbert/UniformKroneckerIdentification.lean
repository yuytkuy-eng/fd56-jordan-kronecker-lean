/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.UniformKroneckerCongruence
import FD56.Hilbert.KroneckerBlock
import FD56.Stabilizer.GenericRows

/-! The uniform corrected forms are a constant signed permutation of Kronecker blocks. -/

noncomputable section
namespace FD56
open Matrix Polynomial

theorem affineMatrixPencil_constant_congruence {K n t : Type*} [Field K]
    [Fintype n] (A B : Matrix n n K) (G : Matrix n t K) :
    (G.map C).transpose * affineMatrixPencil A B * G.map C =
      affineMatrixPencil (G.transpose * A * G) (G.transpose * B * G) := by
  have he (A B : Matrix n n K) :
      affineMatrixPencil A B = A.map C + (X : K[X]) • B.map C := by
    funext i j
    simp [affineMatrixPencil, smul_eq_mul]
  rw [he]
  change (G.map C).transpose * (A.map C + (X : K[X]) • B.map C) * G.map C =
    (G.transpose * A * G).map C + (X : K[X]) • (G.transpose * B * G).map C
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.map_mul, Matrix.transpose_map]

def uniformKroneckerOrder (e r : ℕ) :
    ((Fin e ⊕ Fin (e + 1)) × Fin r) ≃
      ((Fin (e + 1) × Fin r) ⊕ (Fin e × Fin r)) where
  toFun z := z.1.elim (fun h => Sum.inr (h, z.2)) (fun k => Sum.inl (k, z.2))
  invFun z := z.elim (fun k => (Sum.inr k.1, k.2)) (fun h => (Sum.inl h.1, h.2))
  left_inv z := by rcases z with ⟨h | k, j⟩ <;> rfl
  right_inv z := by rcases z with ⟨k, j⟩ | ⟨h, j⟩ <;> rfl

variable {K : Type*} [Field K] (e r : ℕ)

def uniformKroneckerSigns : Matrix ((Fin e ⊕ Fin (e + 1)) × Fin r)
    ((Fin e ⊕ Fin (e + 1)) × Fin r) K :=
  Matrix.diagonal (fun z => (-1 : K) ^ z.1.elim Fin.val Fin.val)

theorem uniformKroneckerSigns_inverse :
    uniformKroneckerSigns (K := K) e r * uniformKroneckerSigns e r = 1 := by
  rw [uniformKroneckerSigns, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    rw [← mul_pow]
    simp
  · simp [Matrix.diagonal_apply, Matrix.one_apply, hij]

def uniformCorrectedPencil :
    Matrix ((Fin (e + 1) × Fin r) ⊕ (Fin e × Fin r))
      ((Fin (e + 1) × Fin r) ⊕ (Fin e × Fin r)) K[X] :=
  affineMatrixPencil
    (Matrix.fromBlocks 0 uniformCrossFirst (-uniformCrossFirst.transpose) 0)
    (Matrix.fromBlocks 0 uniformCrossSecond (-uniformCrossSecond.transpose) 0)

private theorem signed_bidiagonal (h : Fin e) (k : Fin (e + 1)) :
    (-1 : K[X]) ^ h.val *
      ((if k = h.castSucc then X else 0) - (if k = h.succ then 1 else 0)) *
        (-1) ^ k.val = bidiagonalPencil e h k := by
  have hs : (-1 : K[X]) ^ h.val * (-1) ^ h.val = 1 := by
    rw [← mul_pow]
    simp
  by_cases hc : k = h.castSucc
  · subst k
    have hn : h.castSucc ≠ h.succ := by intro hh; have := congrArg Fin.val hh; simp at this
    simp only [if_pos rfl, if_neg hn, sub_zero, bidiagonalPencil, add_zero]
    change (-1 : K[X]) ^ h.val * X * (-1) ^ h.val = X
    calc
      _ = ((-1 : K[X]) ^ h.val * (-1) ^ h.val) * X := by ring
      _ = X := by rw [hs, one_mul]
  · by_cases hn : k = h.succ
    · subst k
      simp only [if_neg hc, if_pos rfl, zero_sub, bidiagonalPencil, zero_add,
        Fin.val_succ, pow_succ, if_true]
      calc
        _ = (-1 : K[X]) ^ h.val * (-1) ^ h.val := by ring
        _ = 1 := hs
    · simp [hc, hn, bidiagonalPencil]

set_option maxHeartbeats 1000000 in
theorem uniform_corrected_pencil_is_kronecker_blocks :
    (uniformKroneckerSigns (K := K) e r).map C *
      (uniformCorrectedPencil e r).submatrix (uniformKroneckerOrder e r) (uniformKroneckerOrder e r) *
      (uniformKroneckerSigns e r).map C =
        Matrix.blockDiagonal (fun _ : Fin r => kroneckerBlockPencil (K := K) e) := by
  classical
  simp only [uniformKroneckerSigns, Matrix.diagonal_map (map_zero C), Matrix.diagonal_mul,
    Matrix.mul_diagonal]
  funext i j
  rcases i with ⟨h | k, a⟩ <;> rcases j with ⟨h' | k', b⟩
  · simp [uniformKroneckerOrder, uniformCorrectedPencil, affineMatrixPencil,
      Matrix.blockDiagonal_apply, kroneckerBlockPencil]
  · by_cases hab : a = b
    · subst b
      simpa [uniformKroneckerOrder, uniformCorrectedPencil, affineMatrixPencil,
        uniformCrossFirst, uniformCrossSecond, uniformNext, uniformCurrent,
        Matrix.one_apply, Matrix.blockDiagonal_apply, kroneckerBlockPencil,
        Prod.mk.injEq, sub_eq_add_neg, add_comm, eq_comm] using signed_bidiagonal (K := K) e h k'
    · simp [uniformKroneckerOrder, uniformCorrectedPencil, affineMatrixPencil,
        uniformCrossFirst, uniformCrossSecond, uniformNext, uniformCurrent,
        Matrix.one_apply, Matrix.blockDiagonal_apply, kroneckerBlockPencil,
        Prod.mk.injEq, hab, Ne.symm hab]
  · by_cases hab : a = b
    · subst b
      have hz : (-1 : K[X]) ^ k.val *
          ((-1) ^ h'.val * ((if k = h'.succ then 1 else 0) +
            -(if k = h'.castSucc then X else 0))) = -bidiagonalPencil e h' k := by
        have ht := signed_bidiagonal (K := K) e h' k
        linear_combination -ht
      simpa [uniformKroneckerOrder, uniformCorrectedPencil, affineMatrixPencil,
        uniformCrossFirst, uniformCrossSecond, uniformNext, uniformCurrent,
        Matrix.one_apply, Matrix.blockDiagonal_apply, kroneckerBlockPencil,
        Prod.mk.injEq, sub_eq_add_neg, add_comm, mul_comm, mul_left_comm, mul_assoc] using hz
    · simp [uniformKroneckerOrder, uniformCorrectedPencil, affineMatrixPencil,
        uniformCrossFirst, uniformCrossSecond, uniformNext, uniformCurrent,
        Matrix.one_apply, Matrix.blockDiagonal_apply, kroneckerBlockPencil,
        Prod.mk.injEq, hab, Ne.symm hab]
  · simp [uniformKroneckerOrder, uniformCorrectedPencil, affineMatrixPencil,
      Matrix.blockDiagonal_apply, kroneckerBlockPencil]

end FD56
