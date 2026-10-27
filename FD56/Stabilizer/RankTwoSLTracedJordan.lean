/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.RankTwoJordanTraceAssembly
import FD56.Stabilizer.RankTwoSLCanonicalTarget

/-! A full SL canonical decomposition from a GL Jordan decomposition and a
sparse trace functional nonzero on every four-dimensional pole summand. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K n m ι : Type*} [Field K] [Fintype n] [Fintype m] [Fintype ι]
  [DecidableEq n] [DecidableEq m] [DecidableEq ι] [Nontrivial ι]

theorem rankTwoSL_canonical_of_sparse_trace
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (s₀ : n)
    (lam : ι → K) (hlam : Function.Injective lam) (k : ι → ℕ) (i₀ : ι)
    (G : Matrix (SLInput n m) (rankTwoJordanSumIndex k) K)
    (H : Matrix (rankTwoJordanSumIndex k) (SLInput n m) K)
    (hGH : G*H=1) (hHG : H*G=1)
    (hcong : (G.map C).transpose*glKirillovMatrix M P*G.map C=rankTwoJordanSumTarget lam k)
    (a b : ι → K) (hab : ∀ i, a i≠0 ∨ b i≠0)
    (htrace : ∀ v, slInputTrace K K (G*ᵥv)=
      ∑ i, (a i*v ⟨i,.inl (.inl 0)⟩+b i*v ⟨i,.inl (.inr 1)⟩)) :
    ∃ T : Matrix (SLChartInput n m s₀) (rankTwoSLCanonicalIndex k) K,
    ∃ S : Matrix (rankTwoSLCanonicalIndex k) (SLChartInput n m s₀) K,
      T*S=1 ∧ S*T=1 ∧
      (T.map C).transpose*slKirillovMatrix M P s₀*T.map C=rankTwoSLCanonicalTarget lam k := by
  obtain ⟨U,V,hUV,hVU,hU,htraceU⟩ := rank_two_jordan_trace_assembly a b lam k hab
  have hGU : (G*U)*(V*H)=1 := by
    rw [Matrix.mul_assoc,← Matrix.mul_assoc U,hUV,Matrix.one_mul,hGH]
  have hVH : (V*H)*(G*U)=1 := by
    rw [Matrix.mul_assoc,← Matrix.mul_assoc H,hHG,Matrix.one_mul,hVU]
  have hcongGU : ((G*U).map C).transpose*glKirillovMatrix M P*(G*U).map C=
      rankTwoJordanSumTarget lam k := by
    rw [Matrix.map_mul,Matrix.transpose_mul]
    calc
      _ = (U.map C).transpose*((G.map C).transpose*glKirillovMatrix M P*G.map C)*U.map C := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hcong]; exact hU
  have htraceGU (v : rankTwoJordanSumIndex k → K) :
      slInputTrace K K ((G*U)*ᵥv)=∑ i, v ⟨i,.inl (.inl 0)⟩ := by
    rw [← Matrix.mulVec_mulVec,htrace,htraceU]
  obtain ⟨R,Q,hRQ,hQR,hR⟩ := rankTwoSL_restriction_of_traced_jordan
    M P s₀ lam hlam k i₀ (G*U) (V*H) hGU hVH hcongGU htraceGU
  exact rankTwoSL_canonical_of_separated M P s₀ lam hlam k i₀ R Q hRQ hQR hR

end FD56
