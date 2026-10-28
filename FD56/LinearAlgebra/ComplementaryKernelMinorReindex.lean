/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.ComplementaryKernelMinors

/-! Complementary maximal minors with arbitrary ambient indices. The kernel
basis is retained; only its completion matrices are reindexed. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {F m r s : Type*} [Field F]
  [Fintype m] [Fintype r] [Fintype s]
  [DecidableEq m] [DecidableEq r] [DecidableEq s]

theorem polynomial_dual_basis_complementary_minors_reindex
    (G : Matrix m r F[X]) (L : Matrix r m F[X]) (hLG : L * G = 1)
    (B : Basis s F[X] (LinearMap.ker (Matrix.toLin' G.transpose)))
    (e : m ≃ r ⊕ s) :
    ∃ c : F, c ≠ 0 ∧ ∀ σ : Equiv.Perm (r ⊕ s),
      (G.submatrix (fun i => e.symm (σ (Sum.inl i))) id).det =
        ((Equiv.Perm.sign σ : ℤ) : F[X]) * C c *
          ((polynomialKernelBasisMatrix G.transpose B).submatrix
            (fun i => e.symm (σ (Sum.inr i))) id).det := by
  have hGL : G.transpose * L.transpose = 1 := by
    rw [← Matrix.transpose_mul, hLG, Matrix.transpose_one]
  obtain ⟨S, _, _, _, _, hHJ⟩ :=
    polynomial_kernel_basis_completion G.transpose L.transpose hGL B
  have h : Matrix.fromCols G S.transpose *
      Matrix.fromRows L (polynomialKernelBasisMatrix G.transpose B).transpose = 1 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_fromRows, Matrix.transpose_fromCols,
      Matrix.transpose_transpose, Matrix.transpose_one] using congrArg Matrix.transpose hHJ
  let J := (Matrix.fromCols G S.transpose).submatrix e.symm id
  let Q := (Matrix.fromRows L (polynomialKernelBasisMatrix G.transpose B).transpose).submatrix
    id e.symm
  have hJQ : J * Q = 1 := by
    dsimp only [J, Q]
    rw [← Matrix.submatrix_mul _ _ e.symm id e.symm Function.bijective_id, h]
    exact Matrix.submatrix_one_equiv e.symm
  have hd : J.det * Q.det = 1 := by
    rw [← Matrix.det_mul, hJQ, Matrix.det_one]
  have hu : IsUnit J.det := isUnit_iff_dvd_one.mpr ⟨_, hd.symm⟩
  obtain ⟨c, hc, he⟩ := Polynomial.isUnit_iff.mp hu
  refine ⟨c, hc.ne_zero, ?_⟩
  intro σ
  have hm := inverse_block_permuted_complementary_det J Q hJQ σ
  have hminor : (Q.submatrix Sum.inr (fun i => σ (Sum.inr i))) =
      ((polynomialKernelBasisMatrix G.transpose B).submatrix
        (fun i => e.symm (σ (Sum.inr i))) id).transpose := rfl
  rw [hminor, Matrix.det_transpose, ← he] at hm
  exact hm

theorem polynomial_dual_basis_selected_complementary_minors
    {K ι : Type*} [Field K] [Algebra K F]
    (G : Matrix m r F[X]) (L : Matrix r m F[X]) (hLG : L * G = 1)
    (B : Basis s F[X] (LinearMap.ker (Matrix.toLin' G.transpose)))
    (e : m ≃ r ⊕ s) (rows : ι → (r ⊕ s ≃ m)) :
    ∃ c : F, c ≠ 0 ∧ ∀ i,
      (G.submatrix (fun j => rows i (Sum.inl j)) id).det =
        C (algebraMap K F (((Equiv.Perm.sign ((rows i).trans e)) : ℤ) : K)) * C c *
          ((polynomialKernelBasisMatrix G.transpose B).submatrix
            (fun j => rows i (Sum.inr j)) id).det := by
  obtain ⟨c, hc, h⟩ := polynomial_dual_basis_complementary_minors_reindex G L hLG B e
  refine ⟨c, hc, ?_⟩
  intro i
  simpa only [Equiv.trans_apply, Equiv.symm_apply_apply, map_intCast] using h ((rows i).trans e)

end FD56
