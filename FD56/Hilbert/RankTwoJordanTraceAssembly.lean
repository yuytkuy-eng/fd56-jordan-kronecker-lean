/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.RankTwoJordanTraceNormalization

/-! Normalize a sparse trace functional on a direct sum of rank-two Jordan pencils. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

theorem rank_two_jordan_trace_assembly (a b lam : ι → K) (k : ι → ℕ)
    (h : ∀ i, a i≠0 ∨ b i≠0) :
    ∃ T S : Matrix (Σ i, rankTwoJordanIndex (k i)) (Σ i, rankTwoJordanIndex (k i)) K,
      T*S=1 ∧ S*T=1 ∧
      (T.map C).transpose*Matrix.blockDiagonal' (fun i => rankTwoJordanPencil (lam i) (k i))*
        T.map C=Matrix.blockDiagonal' (fun i => rankTwoJordanPencil (lam i) (k i)) ∧
      ∀ v, (∑ i, (a i*(T*ᵥv) ⟨i,.inl (.inl 0)⟩+b i*(T*ᵥv) ⟨i,.inl (.inr 1)⟩))=
        ∑ i, v ⟨i,.inl (.inl 0)⟩ := by
  choose U V hUV hVU hU htrace using
    fun i => rank_two_jordan_trace_normalization (a i) (b i) (lam i) (k i) (h i)
  refine ⟨Matrix.blockDiagonal' U,Matrix.blockDiagonal' V,?_,?_,?_,?_⟩
  · rw [← Matrix.blockDiagonal'_mul]
    rw [show (fun i => U i*V i)=(1 : ∀ i, Matrix (rankTwoJordanIndex (k i))
      (rankTwoJordanIndex (k i)) K) from funext hUV,Matrix.blockDiagonal'_one]
  · rw [← Matrix.blockDiagonal'_mul]
    rw [show (fun i => V i*U i)=(1 : ∀ i, Matrix (rankTwoJordanIndex (k i))
      (rankTwoJordanIndex (k i)) K) from funext hVU,Matrix.blockDiagonal'_one]
  · rw [Matrix.blockDiagonal'_map _ _ (map_zero C),Matrix.blockDiagonal'_transpose,
      ← Matrix.blockDiagonal'_mul,← Matrix.blockDiagonal'_mul]
    exact congrArg Matrix.blockDiagonal' (funext hU)
  · have hblock (v : (Σ i, rankTwoJordanIndex (k i)) → K) (i : ι)
        (j : rankTwoJordanIndex (k i)) :
        (Matrix.blockDiagonal' U*ᵥv) ⟨i,j⟩=(U i*ᵥ(fun l => v ⟨i,l⟩)) j := by
      simp only [Matrix.mulVec,dotProduct,Fintype.sum_sigma]
      rw [Fintype.sum_eq_single i]
      · simp
      · intro l hl
        apply Finset.sum_eq_zero
        intro z _
        rw [Matrix.blockDiagonal'_apply_ne _ _ _ hl.symm,zero_mul]
    intro v
    apply Finset.sum_congr rfl
    intro i _
    rw [hblock,hblock]
    exact htrace i (fun j => v ⟨i,j⟩)

end FD56
