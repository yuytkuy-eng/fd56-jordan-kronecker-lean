/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DistinctPoleHyperplane
import FD56.Hilbert.SingleDegreeClosure
import FD56.Hilbert.MixedGLKronecker
import FD56.Hilbert.ScalarCrossVanishing

/-! Kernel and alternation identities for rectangular skew cross pencils. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {R a b : Type*} [CommRing R] [Fintype a] [Fintype b]

theorem skewCrossMatrix_kernel_iff (A : Matrix a b R) (v : a ⊕ b → R) :
    skewCrossMatrix A *ᵥ v=0 ↔
      A *ᵥ (v ∘ Sum.inr)=0 ∧ A.transpose *ᵥ (v ∘ Sum.inl)=0 := by
  constructor
  · intro h
    constructor
    · funext i
      simpa [skewCrossMatrix,Matrix.fromBlocks_mulVec] using congrFun h (.inl i)
    · funext i
      simpa [skewCrossMatrix,Matrix.fromBlocks_mulVec,Matrix.neg_mulVec] using congrFun h (.inr i)
  · rintro ⟨h₀,h₁⟩
    simp [skewCrossMatrix,Matrix.fromBlocks_mulVec,Matrix.neg_mulVec,h₀,h₁]

omit [Fintype a] [Fintype b] in
theorem skewCrossMatrix_skew (A : Matrix a b R) :
    (skewCrossMatrix A).transpose = -skewCrossMatrix A := by
  ext i j
  rcases i with i|i <;> rcases j with j|j <;> simp [skewCrossMatrix]

theorem skewCrossMatrix_alternating (A : Matrix a b R) (v : a ⊕ b → R) :
    v ⬝ᵥ (skewCrossMatrix A *ᵥ v)=0 := by
  have he : v=Sum.elim (v ∘ Sum.inl) (v ∘ Sum.inr) := by ext i; cases i <;> rfl
  conv_lhs => lhs; rw [he]
  simp only [skewCrossMatrix,Matrix.fromBlocks_mulVec,Matrix.zero_mulVec,zero_add,
    Matrix.neg_mulVec,add_zero,sumElim_dotProduct_sumElim,dotProduct_neg,
    Matrix.mulVec_transpose,dotProduct_mulVec]
  rw [dotProduct_comm]
  ring

variable {K : Type*} [Field K]

omit [Fintype a] [Fintype b] in
theorem skewCrossMatrix_coefficient (A : Matrix a b K[X]) (d : ℕ) :
    (Matrix.of fun i j => (skewCrossMatrix A i j).coeff d) =
      skewCrossMatrix (Matrix.of fun i j => (A i j).coeff d) := by
  ext i j
  rcases i with i|i <;> rcases j with j|j <;> simp [skewCrossMatrix]

omit [Fintype a] [Fintype b] in
theorem skewCrossMatrix_degreeBound (A : Matrix a b K[X]) (d : ℕ) (hA : DegreeBound A d) :
    DegreeBound (skewCrossMatrix A) d := by
  intro i j
  rcases i with i|i <;> rcases j with j|j <;>
    simp only [skewCrossMatrix,Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,Matrix.zero_apply,Matrix.neg_apply,
      Matrix.transpose_apply,Polynomial.natDegree_zero,Polynomial.natDegree_neg]
  · exact Nat.zero_le _
  · exact hA i j
  · exact hA j i
  · exact Nat.zero_le _

end FD56
