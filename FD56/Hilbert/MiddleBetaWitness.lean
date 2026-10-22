/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MiddleWitness
import FD56.Hilbert.BetaKernel

/-! Rectangular block pencils have polynomial right inverses and independent
leading rows. Their balanced middle witnesses therefore give beta-kernel profiles. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K r : Type*} [Field K] [Fintype r] [DecidableEq r]

theorem rectangularBlockPencil_right_inverse (e : r → ℕ) :
    ∃ R : Matrix (Σ i, Fin (e i + 1)) (Σ i, Fin (e i)) K[X],
      rectangularBlockPencil (K := K) e * R = 1 := by
  choose R hR using fun i => bidiagonalPencil_right_inverse (K := K) (e i)
  refine ⟨Matrix.blockDiagonal' R, ?_⟩
  rw [rectangularBlockPencil, ← Matrix.blockDiagonal'_mul]
  simp_rw [hR]
  exact Matrix.blockDiagonal'_one

theorem bidiagonalPencil_coeff_one (n : ℕ) (i : Fin n) (j : Fin (n + 1)) :
    (bidiagonalPencil (K := K) n i j).coeff 1 = if j = i.castSucc then 1 else 0 := by
  unfold bidiagonalPencil
  rw [Polynomial.coeff_add]
  split_ifs <;> simp [Polynomial.coeff_one]

theorem rectangularBlockPencil_leading_transpose_injective (e : r → ℕ) :
    Function.Injective (Matrix.mulVec (show Matrix (Σ i, Fin (e i + 1))
      (Σ i, Fin (e i)) K from fun x i => (rectangularBlockPencil e i x).coeff 1)) := by
  have hrow (v : (Σ i, Fin (e i)) → K) (i : r) (k : Fin (e i)) :
      (Matrix.mulVec (fun x j => (rectangularBlockPencil (K := K) e j x).coeff 1) v)
        ⟨i, k.castSucc⟩ = v ⟨i, k⟩ := by
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_sigma]
    rw [Fintype.sum_eq_single i]
    · simp [rectangularBlockPencil, bidiagonalPencil_coeff_one]
    · intro j hj
      apply Finset.sum_eq_zero
      intro x _
      simp [rectangularBlockPencil, Matrix.blockDiagonal'_apply_ne _ _ _ hj]
  intro v w hvw
  funext ⟨i, k⟩
  have hh := congrFun hvw ⟨i, k.castSucc⟩
  simpa only [hrow] using hh

theorem rectangular_block_beta_kernel_finrank
    (e : r → ℕ) (M : Matrix (Σ i, Fin (e i + 1)) (Σ i, Fin (e i + 1)) K[X])
    (hM : DegreeBound M 1) (d : ℕ) :
    Module.finrank K (boundedBetaKernel M (rectangularBlockPencil e) d) =
      Module.finrank K (polynomialKernelAtDegree
        (rectangularBlockPencil e * M * blockMonomialKernel e).transpose d) := by
  obtain ⟨R, hR⟩ := rectangularBlockPencil_right_inverse (K := K) e
  have h := beta_kernel_finrank M (rectangularBlockPencil e) (rectangularBlockKernelBasis e)
      R hR hM (rectangularBlockPencil_degree e)
      (rectangularBlockPencil_leading_transpose_injective e) d
  rw [polynomialKernelBasisMatrix_rectangularBlock (K := K) e] at h
  exact h

theorem exists_affine_middle_balanced_beta_kernel (e : r → ℕ)
    (he : ∀ i j, e i ≤ e j + 1) (hr : Fintype.card r < ∑ i, e i) :
    ∃ M : Matrix (Σ i, Fin (e i + 1)) (Σ i, Fin (e i + 1)) K[X],
      DegreeBound M 1 ∧
      ∀ d, Module.finrank K (boundedBetaKernel M (rectangularBlockPencil e) d) =
        ((∑ i, e i) - Fintype.card r) * (d + 1) - ∑ j, (e j + 2) := by
  obtain ⟨M, hM, hH⟩ := exists_affine_middle_balanced_kernel (K := K) e he hr
  refine ⟨M, hM, ?_⟩
  intro d
  rw [rectangular_block_beta_kernel_finrank e M hM, hH]

end FD56
