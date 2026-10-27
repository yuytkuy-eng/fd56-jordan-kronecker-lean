/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.HalfspaceCompletion
import FD56.LinearAlgebra.PolynomialMatrix
import FD56.LinearAlgebra.AlternatingCongruence

/-! An affine alternating pencil with a constant isotropic halfspace has cross-block form. -/

noncomputable section
namespace FD56
open Matrix Polynomial

theorem constant_isotropic_halfspace_block_form {K a : Type*} [Field K]
    [Fintype a] [DecidableEq a] (d : ℕ) (P : Matrix a a K[X])
    (hdegree : DegreeBound P 1) (hskew : P.transpose = -P)
    (halt : ∀ v, v ⬝ᵥ (P*ᵥv)=0)
    (Q : Matrix a (Fin d) K) (hinj : Function.Injective Q.mulVec)
    (hiso : (Q.map C).transpose*P*Q.map C=0) (hdim : Fintype.card a=2*d) :
    ∃ S : Matrix a (Fin d ⊕ Fin d) K,
    ∃ T : Matrix (Fin d ⊕ Fin d) a K,
    ∃ A W : Matrix (Fin d) (Fin d) K[X],
      S*T=1 ∧ T*S=1 ∧
      (S.map C).transpose*P*S.map C=Matrix.fromBlocks A W (-W.transpose) 0 ∧
      DegreeBound A 1 ∧ DegreeBound W 1 ∧
      ∀ k (v : Fin d → K), v ⬝ᵥ ((fun i j => (A i j).coeff k)*ᵥv)=0 := by
  obtain ⟨S,T,hST,hTS,hSQ⟩ := injective_half_matrix_completion d Q hinj hdim
  let H := (S.map C).transpose*P*S.map C
  let U := S.submatrix id Sum.inl
  let A := H.submatrix Sum.inl Sum.inl
  let W := H.submatrix Sum.inl Sum.inr
  have hSdegree : DegreeBound (S.map C) 0 := by intro i j; simp
  have hHdegree : DegreeBound H 1 := by
    simpa using degreeBound_mul (degreeBound_mul (fun i j => hSdegree j i) hdegree) hSdegree
  have hHskew : H.transpose = -H := by
    simp only [H,Matrix.transpose_mul,Matrix.transpose_transpose,hskew,
      Matrix.mul_neg,Matrix.neg_mul,Matrix.mul_assoc]
  have hproject (f g : Fin d → Fin d ⊕ Fin d) :
      H.submatrix f g=((S.submatrix id f).map C).transpose*P*(S.submatrix id g).map C := by
    simp only [← Matrix.submatrix_map,Matrix.transpose_submatrix]
    change H.submatrix f g=(S.map C).transpose.submatrix f (Equiv.refl a)*
      P.submatrix (Equiv.refl a) (Equiv.refl a)*(S.map C).submatrix (Equiv.refl a) g
    rw [Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv]
  have hzero : H.submatrix Sum.inr Sum.inr=0 := by rw [hproject,hSQ,hiso]
  refine ⟨S,T,A,W,hST,hTS,?_,(fun i j => hHdegree _ _),(fun i j => hHdegree _ _),?_⟩
  · change H=Matrix.fromBlocks A W (-W.transpose) 0
    funext i j
    cases i with
    | inl i => cases j <;> rfl
    | inr i =>
      cases j with
      | inl j =>
        have h := congrFun (congrFun hHskew (Sum.inl j)) (Sum.inr i)
        exact h
      | inr j => exact congrFun (congrFun hzero i) j
  · intro k v
    have hA : A=(U.map C).transpose*P*U.map C := hproject Sum.inl Sum.inl
    have h := matrix_congruence_alternating P (U.map C) halt (fun i => C (v i))
    rw [← hA] at h
    have hc := congrArg (fun p : K[X] => p.coeff k) h
    simpa only [dotProduct,Matrix.mulVec,Polynomial.finset_sum_coeff,
      Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_zero] using hc

end FD56
