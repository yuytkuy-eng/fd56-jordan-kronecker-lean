/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.RankTwoJordanGrouping
import FD56.Stabilizer.SquareSLTraceChart
import FD56.Hilbert.DistinctPoleKernel

/-! Coordinates for the trace hyperplane with arbitrary simple Jordan tails. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

abbrev rankTwoSLGroupedIndex (j : n → ℕ) (i₀ : n) :=
  ((({i : n // i≠i₀} ⊕ n) ⊕ (n ⊕ n)) ⊕ rankTwoJordanTailIndex j)

def rankTwoSLGroupedEmbedding (j : n → ℕ) (i₀ : n) :
    Matrix (rankTwoJordanGroupedIndex j) (rankTwoSLGroupedIndex j i₀) K :=
  Matrix.fromBlocks (Matrix.fromBlocks (Matrix.fromBlocks (poleTraceChart i₀) 0 0 1) 0 0 1) 0 0 1

def rankTwoSLGroupedRetraction (j : n → ℕ) (i₀ : n) :
    Matrix (rankTwoSLGroupedIndex j i₀) (rankTwoJordanGroupedIndex j) K :=
  Matrix.fromBlocks (Matrix.fromBlocks (Matrix.fromBlocks (poleTraceRetraction i₀) 0 0 1) 0 0 1) 0 0 1

theorem rankTwoSLGroupedRetraction_embedding (j : n → ℕ) (i₀ : n) :
    rankTwoSLGroupedRetraction (K := K) j i₀*rankTwoSLGroupedEmbedding (K := K) j i₀=1 := by
  simp [rankTwoSLGroupedRetraction,rankTwoSLGroupedEmbedding,Matrix.fromBlocks_multiply,
    poleTraceRetraction_chart,Matrix.fromBlocks_one]

theorem rankTwoSLGroupedEmbedding_trace (j : n → ℕ) (i₀ : n)
    (v : rankTwoSLGroupedIndex j i₀ → K) :
    ∑ i, (rankTwoSLGroupedEmbedding (K := K) j i₀*ᵥv) (.inl (.inl (.inl i)))=0 := by
  simpa only [rankTwoSLGroupedEmbedding,Matrix.fromBlocks_mulVec,Matrix.zero_mulVec,
    add_zero,Sum.elim_inl] using poleTraceChart_mulVec_sum i₀ (fun i => v (.inl (.inl (.inl i))))

theorem rankTwoSLGroupedEmbedding_retraction (j : n → ℕ) (i₀ : n)
    (v : rankTwoJordanGroupedIndex j → K) (hv : ∑ i, v (.inl (.inl (.inl i)))=0) :
    rankTwoSLGroupedEmbedding (K := K) j i₀*ᵥ(rankTwoSLGroupedRetraction j i₀*ᵥv)=v := by
  have h := poleTraceChart_retraction i₀ (fun i => v (.inl (.inl (.inl i)))) hv
  funext i
  rcases i with ((i|i)|(i|i))|i
  all_goals simp only [rankTwoSLGroupedEmbedding,rankTwoSLGroupedRetraction,Matrix.fromBlocks_mulVec,
    Matrix.zero_mulVec,Matrix.one_mulVec,add_zero,zero_add,Sum.elim_inl,Sum.elim_inr,
    Function.comp_apply]
  exact congrFun h i

end FD56
