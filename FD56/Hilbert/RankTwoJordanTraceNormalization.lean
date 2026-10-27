/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.JordanFourTraceNormalization

/-! Trace normalization preserves a rank-two Jordan block and its simple tails. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K : Type*} [Field K]

theorem rank_two_jordan_trace_normalization (a b lam : K) (k : ℕ)
    (h : a≠0 ∨ b≠0) :
    ∃ T S : Matrix (rankTwoJordanIndex k) (rankTwoJordanIndex k) K,
      T*S=1 ∧ S*T=1 ∧
      (T.map C).transpose*rankTwoJordanPencil lam k*T.map C=rankTwoJordanPencil lam k ∧
      ∀ v, a*(T*ᵥv) (.inl (.inl 0))+b*(T*ᵥv) (.inl (.inr 1))=v (.inl (.inl 0)) := by
  obtain ⟨U,V,hUV,hVU,hU,htrace⟩ := jordan_four_trace_normalization a b lam h
  let T : Matrix (rankTwoJordanIndex k) (rankTwoJordanIndex k) K :=
    Matrix.fromBlocks U 0 0 1
  let S : Matrix (rankTwoJordanIndex k) (rankTwoJordanIndex k) K :=
    Matrix.fromBlocks V 0 0 1
  refine ⟨T,S,?_,?_,?_,?_⟩
  · simp [T,S,Matrix.fromBlocks_multiply,hUV,Matrix.fromBlocks_one]
  · simp [T,S,Matrix.fromBlocks_multiply,hVU,Matrix.fromBlocks_one]
  · simp only [T,rankTwoJordanPencil,Matrix.fromBlocks_map,
      Matrix.map_zero _ (map_zero C),Matrix.map_one _ (map_zero C) (map_one C),
      Matrix.fromBlocks_transpose,Matrix.transpose_zero,Matrix.transpose_one,
      Matrix.fromBlocks_multiply,Matrix.mul_zero,Matrix.zero_mul,zero_add,add_zero,
      Matrix.one_mul,Matrix.mul_one,hU]
  · intro v
    simpa only [T,Matrix.fromBlocks_mulVec,Matrix.zero_mulVec,add_zero,Sum.elim_inl]
      using htrace (fun i => v (.inl i))

end FD56
