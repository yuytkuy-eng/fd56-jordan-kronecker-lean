/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.RankTwoTraceSupportDegree

/-! Coordinate evaluation of the sparse trace covector. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

theorem rankTwoTraceSumCovector_dotProduct (a b : ι → K) (k : ℕ)
    (v : (Σ _ : ι, rankTwoJordanIndex k) → K) :
    rankTwoTraceSumCovector a b k ⬝ᵥ v =
      ∑ i : ι, (a i*v ⟨i,Sum.inl (Sum.inl 0)⟩ + b i*v ⟨i,Sum.inl (Sum.inr 1)⟩) := by
  simp [rankTwoTraceSumCovector,rankTwoTraceCovector,dotProduct,Fintype.sum_sigma,
    Fintype.sum_sum_type,Fin.sum_univ_succ]

end FD56
