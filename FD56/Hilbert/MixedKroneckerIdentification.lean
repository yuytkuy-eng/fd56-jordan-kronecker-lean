/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.MixedKroneckerCongruence
import FD56.Hilbert.UniformKroneckerIdentification

/-! A signed permutation identifies mixed corrected forms with standard Kronecker blocks. -/

noncomputable section
namespace FD56
open Matrix Polynomial

def mixedKroneckerOrder {r : ℕ} (d : Fin r → ℕ) :
    (Σ j, Fin (d j) ⊕ Fin (d j + 1)) ≃
      ((Σ j, Fin (d j + 1)) ⊕ (Σ j, Fin (d j))) where
  toFun z := z.2.elim (fun h => Sum.inr ⟨z.1,h⟩) (fun k => Sum.inl ⟨z.1,k⟩)
  invFun z := z.elim (fun k => ⟨k.1,Sum.inr k.2⟩) (fun h => ⟨h.1,Sum.inl h.2⟩)
  left_inv z := by rcases z with ⟨j,h | k⟩ <;> rfl
  right_inv z := by rcases z with ⟨j,k⟩ | ⟨j,h⟩ <;> rfl

variable {K : Type*} [Field K] {r : ℕ}

def mixedKroneckerSigns (d : Fin r → ℕ) :
    Matrix (Σ j, Fin (d j) ⊕ Fin (d j + 1)) (Σ j, Fin (d j) ⊕ Fin (d j + 1)) K :=
  Matrix.diagonal (fun z => (-1 : K) ^ z.2.elim Fin.val Fin.val)

theorem mixedKroneckerSigns_inverse (d : Fin r → ℕ) :
    mixedKroneckerSigns (K := K) d * mixedKroneckerSigns d = 1 := by
  rw [mixedKroneckerSigns, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    rw [← mul_pow]
    simp
  · simp [Matrix.diagonal_apply, Matrix.one_apply, hij]

def mixedCorrectedPencil (d : Fin r → ℕ) :
    Matrix ((Σ j, Fin (d j + 1)) ⊕ (Σ j, Fin (d j)))
      ((Σ j, Fin (d j + 1)) ⊕ (Σ j, Fin (d j))) K[X] :=
  affineMatrixPencil
    (Matrix.fromBlocks 0 (mixedCrossFirst d) (-(mixedCrossFirst d).transpose) 0)
    (Matrix.fromBlocks 0 (mixedCrossSecond d) (-(mixedCrossSecond d).transpose) 0)

variable (e : ℕ)

private theorem mixed_signed_bidiagonal (h : Fin e) (k : Fin (e + 1)) :
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


theorem mixed_corrected_pencil_is_kronecker_blocks (d : Fin r → ℕ) :
    (mixedKroneckerSigns (K := K) d).map C *
      (mixedCorrectedPencil d).submatrix (mixedKroneckerOrder d) (mixedKroneckerOrder d) *
      (mixedKroneckerSigns d).map C =
        Matrix.blockDiagonal' (fun j => kroneckerBlockPencil (K := K) (d j)) := by
  classical
  simp only [mixedKroneckerSigns, Matrix.diagonal_map (map_zero C), Matrix.diagonal_mul,
    Matrix.mul_diagonal]
  funext i j
  rcases i with ⟨a,hi⟩
  rcases j with ⟨b,hj⟩
  by_cases hab : a = b
  · subst b
    rcases hi with h | k <;> rcases hj with h' | k'
    · simp [mixedKroneckerOrder, mixedCorrectedPencil, affineMatrixPencil,
        Matrix.blockDiagonal'_apply_eq, kroneckerBlockPencil]
    · simpa [mixedKroneckerOrder, mixedCorrectedPencil, affineMatrixPencil,
        mixedCrossFirst, mixedCrossSecond, mixedNext, mixedCurrent,
        Matrix.one_apply, Matrix.blockDiagonal'_apply_eq, kroneckerBlockPencil,
        Sigma.mk.inj_iff, sub_eq_add_neg, add_comm, eq_comm] using
        mixed_signed_bidiagonal (K := K) (d a) h k'
    · have hz : (-1 : K[X]) ^ k.val *
          ((-1) ^ h'.val * ((if k = h'.succ then 1 else 0) +
            -(if k = h'.castSucc then X else 0))) = -bidiagonalPencil (d a) h' k := by
        have ht := mixed_signed_bidiagonal (K := K) (d a) h' k
        linear_combination -ht
      simpa [mixedKroneckerOrder, mixedCorrectedPencil, affineMatrixPencil,
        mixedCrossFirst, mixedCrossSecond, mixedNext, mixedCurrent,
        Matrix.one_apply, Matrix.blockDiagonal'_apply_eq, kroneckerBlockPencil,
        Sigma.mk.inj_iff, sub_eq_add_neg, add_comm, mul_comm, mul_left_comm, mul_assoc] using hz
    · simp [mixedKroneckerOrder, mixedCorrectedPencil, affineMatrixPencil,
        Matrix.blockDiagonal'_apply_eq, kroneckerBlockPencil]
  · rcases hi with h | k <;> rcases hj with h' | k'
    all_goals
      simp [mixedKroneckerOrder, mixedCorrectedPencil, affineMatrixPencil,
        mixedCrossFirst, mixedCrossSecond, mixedNext, mixedCurrent,
        Matrix.one_apply, Matrix.blockDiagonal'_apply_ne, kroneckerBlockPencil,
        Sigma.mk.inj_iff, hab, Ne.symm hab]

end FD56
