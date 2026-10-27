/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SingleKroneckerBlock

/-! A singleton Kronecker restriction supplies independent constant isotropic columns. -/

noncomputable section
namespace FD56
open Matrix Polynomial

theorem single_block_restriction_isotropic_columns {K a b : Type*} [Field K]
    [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (P : Matrix a a K[X]) (E : Matrix a b K) (L : Matrix b a K)
    (hLE : L*E=1) (e : ℕ)
    (hP : HasKroneckerDecomposition ((E.map C).transpose*P*E.map C) [e]) :
    ∃ Q : Matrix a (Fin (e+1)) K,
      Function.Injective Q.mulVec ∧ (Q.map C).transpose*P*Q.map C=0 := by
  obtain ⟨T,S,hTS,hST,hcong⟩ := single_kronecker_block_congruence _ e hP
  let Q := (E*T).submatrix id Sum.inr
  let J := (S*L).submatrix Sum.inr id
  have hJQ : J*Q=1 := by
    change (S*L).submatrix Sum.inr (Equiv.refl a) *
      (E*T).submatrix (Equiv.refl a) Sum.inr=1
    rw [Matrix.submatrix_mul_equiv]
    have h : (S*L)*(E*T)=1 := by
      calc
        (S*L)*(E*T)=S*(L*E)*T := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hLE,Matrix.mul_one,hST]
    rw [h]
    exact Matrix.submatrix_one Sum.inr Sum.inr_injective
  refine ⟨Q,?_,?_⟩
  · intro v w hvw
    have h := congrArg J.mulVec hvw
    simpa only [Matrix.mulVec_mulVec,hJQ,Matrix.one_mulVec] using h
  · have hbig : ((E*T).map C).transpose*P*(E*T).map C=kroneckerBlockPencil e := by
      rw [Matrix.map_mul,Matrix.transpose_mul]
      simpa only [Matrix.mul_assoc] using hcong
    change (((E*T).submatrix id Sum.inr).map C).transpose*P*
      ((E*T).submatrix id Sum.inr).map C = 0
    simp only [← Matrix.submatrix_map,Matrix.transpose_submatrix]
    change ((E*T).map C).transpose.submatrix Sum.inr (Equiv.refl a) *
      P.submatrix (Equiv.refl a) (Equiv.refl a) *
      ((E*T).map C).submatrix (Equiv.refl a) Sum.inr=0
    rw [Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv,hbig]
    funext i j
    simp [kroneckerBlockPencil]

end FD56
