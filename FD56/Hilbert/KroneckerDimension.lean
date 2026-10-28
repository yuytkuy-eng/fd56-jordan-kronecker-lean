/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MixedGLKronecker

/-! A complete Kronecker congruence exhausts the ambient dimension. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

theorem kronecker_decomposition_dimension (H : Matrix n n K[X]) (xs : List ℕ)
    (h : HasKroneckerDecomposition H xs) :
    Fintype.card n=(xs.map (fun e => 2*e+1)).sum := by
  obtain ⟨r,d,hp,T,S,hTS,hST,_⟩ := h
  let E : (n → K) ≃ₗ[K] ((Σ j, Fin (d j) ⊕ Fin (d j+1)) → K) :=
    { Matrix.toLin' S with
      invFun := Matrix.toLin' T
      left_inv := by
        intro v
        change T *ᵥ (S *ᵥ v)=v
        rw [Matrix.mulVec_mulVec,hTS,Matrix.one_mulVec]
      right_inv := by
        intro v
        change S *ᵥ (T *ᵥ v)=v
        rw [Matrix.mulVec_mulVec,hST,Matrix.one_mulVec] }
  have hc := E.finrank_eq
  simp only [Module.finrank_fintype_fun_eq_card,Fintype.card_sigma,
    Fintype.card_sum,Fintype.card_fin] at hc
  rw [← (hp.map (fun e => 2*e+1)).sum_eq,List.map_ofFn,List.sum_ofFn]
  rw [hc]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Function.comp_apply]
  omega

end FD56
