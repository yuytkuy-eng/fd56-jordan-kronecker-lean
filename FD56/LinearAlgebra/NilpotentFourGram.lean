/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.NilpotentFourNormalForm
import FD56.LinearAlgebra.AlternatingCongruence

/-! Four explicit columns spanning the nondegenerate part of a square-zero pair. -/

noncomputable section
namespace FD56
open Matrix

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

def nilpotentFourColumns (N : Matrix n n K) (a b : n → K) :
    Matrix n (Fin 2 ⊕ Fin 2) K :=
  fun i => Sum.elim ![a i,b i] ![(N *ᵥ a) i,(N *ᵥ b) i]

theorem nilpotent_four_self_adjoint (B N : Matrix n n K)
    (hB : ∀ v, v ⬝ᵥ (B *ᵥ v)=0)
    (hBN : ∀ v, v ⬝ᵥ ((B*N) *ᵥ v)=0) : N.transpose*B=B*N := by
  have ht := alternating_matrix_transpose (B*N) hBN
  rw [Matrix.transpose_mul,alternating_matrix_transpose B hB,Matrix.mul_neg] at ht
  exact neg_injective ht

omit [DecidableEq n] in
private theorem pair_swap (B : Matrix n n K)
    (hB : ∀ v, v ⬝ᵥ (B *ᵥ v)=0) (u v : n → K) :
    u ⬝ᵥ (B *ᵥ v)=-(v ⬝ᵥ (B *ᵥ u)) := by
  have hh := hB (u+v)
  simp only [Matrix.mulVec_add,add_dotProduct,dotProduct_add,hB,zero_add,add_zero] at hh
  exact eq_neg_of_add_eq_zero_left ((add_comm _ _).trans hh)

omit [DecidableEq n] in
private theorem gram_entry {a : Type*} [Fintype a] (B : Matrix n n K)
    (Q : Matrix n a K) (i j : a) :
    (Q.transpose*B*Q) i j=(fun k => Q k i) ⬝ᵥ (B *ᵥ (fun k => Q k j)) := by
  change ((Q.transpose*B) *ᵥ (fun k => Q k j)) i=_
  rw [← Matrix.mulVec_mulVec]
  rfl

theorem nilpotent_four_gram_pair (B N : Matrix n n K) (a b : n → K)
    (hB : ∀ v, v ⬝ᵥ (B *ᵥ v)=0)
    (hBN : ∀ v, v ⬝ᵥ ((B*N) *ᵥ v)=0)
    (hsq : N*N=0) (hpair : a ⬝ᵥ (B *ᵥ (N *ᵥ b))=1) :
    (nilpotentFourColumns N a b).transpose*B*nilpotentFourColumns N a b=
        nilpotentFourGram (a ⬝ᵥ (B *ᵥ b)) ∧
    (nilpotentFourColumns N a b).transpose*(B*N)*nilpotentFourColumns N a b=
        nilpotentFourShift := by
  have hn (v : n → K) : N *ᵥ (N *ᵥ v)=0 := by
    rw [Matrix.mulVec_mulVec,hsq,Matrix.zero_mulVec]
  have hself (u v : n → K) :
      (N *ᵥ u) ⬝ᵥ (B *ᵥ v)=u ⬝ᵥ (B *ᵥ (N *ᵥ v)) := by
    calc
      _ = -(v ⬝ᵥ (B *ᵥ (N *ᵥ u))) := pair_swap B hB _ _
      _ = -(v ⬝ᵥ ((B*N) *ᵥ u)) := by rw [Matrix.mulVec_mulVec]
      _ = -(-(u ⬝ᵥ ((B*N) *ᵥ v))) := by rw [pair_swap (B*N) hBN v u]
      _ = _ := by rw [neg_neg,← Matrix.mulVec_mulVec]
  have hdiag (v : n → K) : v ⬝ᵥ (B *ᵥ (N *ᵥ v))=0 := by
    rw [Matrix.mulVec_mulVec,hBN]
  have hflip : b ⬝ᵥ (B *ᵥ (N *ᵥ a)) = -1 := by
    rw [Matrix.mulVec_mulVec,pair_swap (B*N) hBN b a,← Matrix.mulVec_mulVec,hpair]
  constructor
  · ext i j
    rw [gram_entry]
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;>
      simp [nilpotentFourColumns,nilpotentFourGram,Sum.elim_inl,Sum.elim_inr,
        Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,
        Matrix.zero_apply,← Matrix.mulVec_mulVec,hB,hself,hdiag,hpair,hflip,hn,Matrix.mulVec_zero,dotProduct_zero]
    exact pair_swap B hB b a
  · ext i j
    rw [gram_entry]
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;>
      simp [nilpotentFourColumns,nilpotentFourShift,Sum.elim_inl,Sum.elim_inr,
        Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,
        Matrix.zero_apply,← Matrix.mulVec_mulVec,hB,hself,hdiag,hpair,hflip,hn,
        Matrix.mulVec_zero,dotProduct_zero]

theorem nilpotent_four_gram_det (B N : Matrix n n K) (a b : n → K)
    (hB : ∀ v, v ⬝ᵥ (B *ᵥ v)=0)
    (hBN : ∀ v, v ⬝ᵥ ((B*N) *ᵥ v)=0)
    (hsq : N*N=0) (hpair : a ⬝ᵥ (B *ᵥ (N *ᵥ b))=1) :
    ((nilpotentFourColumns N a b).transpose*B*nilpotentFourColumns N a b).det=1 := by
  rw [(nilpotent_four_gram_pair B N a b hB hBN hsq hpair).1,nilpotentFourGram_det]

end FD56
