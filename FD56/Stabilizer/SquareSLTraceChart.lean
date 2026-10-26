/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.SquareGLJordanGrouping
import FD56.Hilbert.DistinctPoleKernel

/-! Coordinates for the sum-zero hyperplane in the grouped square pencil. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

def poleTraceRetraction (i₀ : n) : Matrix {j : n // j≠i₀} n K :=
  (1 : Matrix n n K).submatrix Subtype.val id

theorem poleTraceRetraction_mulVec (i₀ : n) (v : n → K) (j : {j : n // j≠i₀}) :
    (poleTraceRetraction (K := K) i₀*ᵥv) j=v j.val := by
  simp [poleTraceRetraction,Matrix.mulVec,dotProduct,Matrix.one_apply]

theorem poleTraceChart_mulVec_nonpivot (i₀ : n) (v : {j : n // j≠i₀} → K)
    (j : {j : n // j≠i₀}) : (poleTraceChart (K := K) i₀*ᵥv) j.val=v j := by
  simp only [Matrix.mulVec,dotProduct,poleTraceChart,j.property,if_false,sub_zero]
  have he (i : {j : n // j≠i₀}) : j.val=i.val ↔ j=i := Subtype.val_inj
  simp [he,ite_mul]

theorem poleTraceChart_mulVec_sum (i₀ : n) (v : {j : n // j≠i₀} → K) :
    ∑ i, (poleTraceChart (K := K) i₀*ᵥv) i=0 := by
  simp only [Matrix.mulVec,dotProduct]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul,poleTraceChart_sum,zero_mul,Finset.sum_const_zero]

theorem poleTraceRetraction_chart (i₀ : n) :
    poleTraceRetraction (K := K) i₀*poleTraceChart (K := K) i₀=1 := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  change (poleTraceRetraction i₀*poleTraceChart i₀)*ᵥv=(1 : Matrix _ _ K)*ᵥv
  rw [← Matrix.mulVec_mulVec,Matrix.one_mulVec]
  funext j
  rw [poleTraceRetraction_mulVec,poleTraceChart_mulVec_nonpivot]

theorem poleTraceChart_retraction (i₀ : n) (v : n → K) (hv : ∑ i, v i=0) :
    poleTraceChart (K := K) i₀*ᵥ(poleTraceRetraction i₀*ᵥv)=v := by
  let w := poleTraceChart (K := K) i₀*ᵥ(poleTraceRetraction i₀*ᵥv)
  have he (i : n) (hi : i≠i₀) : w i=v i := by
    exact (poleTraceChart_mulVec_nonpivot i₀ _ ⟨i,hi⟩).trans
      (poleTraceRetraction_mulVec i₀ v ⟨i,hi⟩)
  have hs : ∑ i, (w i-v i)=0 := by
    rw [Finset.sum_sub_distrib,poleTraceChart_mulVec_sum,hv,sub_self]
  have hp : w i₀=v i₀ := by
    rw [Finset.sum_eq_single i₀] at hs
    · exact sub_eq_zero.mp hs
    · intro i _ hi
      rw [he i hi,sub_self]
    · simp
  funext i
  by_cases hi : i=i₀
  · subst i; exact hp
  · exact he i hi

abbrev squareSLGroupedIndex (j : n → n) (i₀ : n) :=
  ((({i : n // i≠i₀} ⊕ n) ⊕ (n ⊕ n)) ⊕ squareGLTailIndex j)

def squareSLGroupedEmbedding (j : n → n) (i₀ : n) :
    Matrix (squareGLGroupedIndex j) (squareSLGroupedIndex j i₀) K :=
  Matrix.fromBlocks (Matrix.fromBlocks (Matrix.fromBlocks (poleTraceChart i₀) 0 0 1) 0 0 1) 0 0 1

def squareSLGroupedRetraction (j : n → n) (i₀ : n) :
    Matrix (squareSLGroupedIndex j i₀) (squareGLGroupedIndex j) K :=
  Matrix.fromBlocks (Matrix.fromBlocks (Matrix.fromBlocks (poleTraceRetraction i₀) 0 0 1) 0 0 1) 0 0 1

theorem squareSLGroupedRetraction_embedding (j : n → n) (i₀ : n) :
    squareSLGroupedRetraction (K := K) j i₀*squareSLGroupedEmbedding (K := K) j i₀=1 := by
  simp [squareSLGroupedRetraction,squareSLGroupedEmbedding,Matrix.fromBlocks_multiply,
    poleTraceRetraction_chart,Matrix.fromBlocks_one]

theorem squareSLGroupedEmbedding_trace (j : n → n) (i₀ : n)
    (v : squareSLGroupedIndex j i₀ → K) :
    ∑ i, (squareSLGroupedEmbedding (K := K) j i₀*ᵥv) (.inl (.inl (.inl i)))=0 := by
  simpa only [squareSLGroupedEmbedding,Matrix.fromBlocks_mulVec,Matrix.zero_mulVec,
    add_zero,Sum.elim_inl] using poleTraceChart_mulVec_sum i₀ (fun i => v (.inl (.inl (.inl i))))

theorem squareSLGroupedEmbedding_retraction (j : n → n) (i₀ : n)
    (v : squareGLGroupedIndex j → K) (hv : ∑ i, v (.inl (.inl (.inl i)))=0) :
    squareSLGroupedEmbedding (K := K) j i₀*ᵥ(squareSLGroupedRetraction j i₀*ᵥv)=v := by
  have h := poleTraceChart_retraction i₀ (fun i => v (.inl (.inl (.inl i)))) hv
  funext i
  rcases i with ((i|i)|(i|i))|i
  all_goals simp only [squareSLGroupedEmbedding,squareSLGroupedRetraction,Matrix.fromBlocks_mulVec,
    Matrix.zero_mulVec,Matrix.one_mulVec,add_zero,zero_add,Sum.elim_inl,Sum.elim_inr,
    Function.comp_apply]
  exact congrFun h i

end FD56
