/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.RankTwoSLTraceChart
import FD56.Stabilizer.SLTraceTransport

/-! Restrict a trace-normalized Jordan sum with arbitrary simple tails. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

def rankTwoSLSeparatedTarget (lam : n → K) (j : n → ℕ) (i₀ : n) :
    Matrix (rankTwoSLGroupedIndex j i₀) (rankTwoSLGroupedIndex j i₀) K[X] :=
  Matrix.fromBlocks
    (Matrix.fromBlocks (skewCrossMatrix (poleTracePencil lam i₀)) 0 0
      (skewCrossMatrix (regularPoleDiagonal lam))) 0 0 (rankTwoJordanTailTarget lam j)

def rankTwoSLPairOrder (j : n → ℕ) (i₀ : n) :
    rankTwoSLGroupedIndex j i₀ ≃ rankTwoSLGroupedIndex j i₀ :=
  Equiv.sumCongr (Equiv.sumSumSumComm {i : n // i≠i₀} n n n) (Equiv.refl _)

omit [Fintype n] in
theorem rankTwoSLGroupedEmbedding_map {L : Type*} [Field L] (f : K →+* L)
    (j : n → ℕ) (i₀ : n) :
    (rankTwoSLGroupedEmbedding (K := K) j i₀).map f=rankTwoSLGroupedEmbedding j i₀ := by
  have h : (poleTraceChart (K := K) i₀).map f=poleTraceChart (K := L) i₀ := by
    funext i k
    simp only [Matrix.map_apply,poleTraceChart,map_sub]
    split_ifs <;> simp
  simp only [rankTwoSLGroupedEmbedding,Matrix.fromBlocks_map,h,
    Matrix.map_zero _ (map_zero f),Matrix.map_one _ (map_zero f) (map_one f)]

theorem rankTwoSLGroupedEmbedding_restrict (lam : n → K) (j : n → ℕ) (i₀ : n) :
    ((rankTwoSLGroupedEmbedding (K := K) j i₀).map C).transpose *
        Matrix.fromBlocks (skewCrossMatrix (Matrix.fromBlocks (regularPoleDiagonal lam)
          (allOnesMatrix n K[X]) 0 (regularPoleDiagonal lam))) 0 0 (rankTwoJordanTailTarget lam j) *
        (rankTwoSLGroupedEmbedding j i₀).map C =
      Matrix.fromBlocks
        (skewCrossMatrix (Matrix.fromBlocks (poleTracePencil lam i₀) 0 0 (regularPoleDiagonal lam)))
        0 0 (rankTwoJordanTailTarget lam j) := by
  let E : Matrix (n ⊕ n) ({i : n // i≠i₀} ⊕ n) K[X] :=
    Matrix.fromBlocks ((poleTraceChart (K := K) i₀).map C) 0 0 1
  have hE : E.transpose * Matrix.fromBlocks (regularPoleDiagonal lam) (allOnesMatrix n K[X])
      0 (regularPoleDiagonal lam)=Matrix.fromBlocks (poleTracePencil lam i₀) 0 0 (regularPoleDiagonal lam) :=
    distinctPole_hyperplane_cross lam _ (poleTraceChart_sum i₀)
  have hmap : (rankTwoSLGroupedEmbedding (K := K) j i₀).map C=
      Matrix.fromBlocks (Matrix.fromBlocks E 0 0 1) 0 0 1 := by
    simp only [rankTwoSLGroupedEmbedding,Matrix.fromBlocks_map,E,
      Matrix.map_zero _ (map_zero C),Matrix.map_one _ (map_zero C) (map_one C)]
  rw [hmap]
  simp only [Matrix.fromBlocks_transpose,Matrix.transpose_zero,Matrix.transpose_one,
    Matrix.fromBlocks_multiply,Matrix.mul_zero,Matrix.zero_mul,zero_add,add_zero,
    Matrix.one_mul,Matrix.mul_one]
  have hcore := skewCross_restrict_first E
    (Matrix.fromBlocks (regularPoleDiagonal lam) (allOnesMatrix n K[X]) 0 (regularPoleDiagonal lam))
  rw [hE] at hcore
  simpa only [Matrix.fromBlocks_transpose,Matrix.transpose_zero,Matrix.transpose_one] using
    congrArg (fun Z => Matrix.fromBlocks Z 0 0 (rankTwoJordanTailTarget lam j)) hcore

theorem rankTwoSLSeparatedTarget_reindex (lam : n → K) (j : n → ℕ) (i₀ : n) :
    (Matrix.fromBlocks
      (skewCrossMatrix (Matrix.fromBlocks (poleTracePencil lam i₀) 0 0 (regularPoleDiagonal lam)))
      0 0 (rankTwoJordanTailTarget lam j)).submatrix (rankTwoSLPairOrder j i₀) (rankTwoSLPairOrder j i₀) =
      rankTwoSLSeparatedTarget lam j i₀ := by
  funext u v
  rcases u with ((i|i)|(i|i))|i <;> rcases v with ((k|k)|(k|k))|k <;>
    simp [rankTwoSLSeparatedTarget,rankTwoSLPairOrder,Equiv.sumSumSumComm,skewCrossMatrix]

theorem rankTwoSL_restriction_of_traced_jordan
    {u v : Type*} [Fintype u] [Fintype v] [DecidableEq u] [DecidableEq v]
    (M : Matrix u u K[X]) (P : Matrix v u K[X]) (s₀ : u)
    (lam : n → K) (hlam : Function.Injective lam) (j : n → ℕ) (i₀ : n)
    (G : Matrix (SLInput u v) (rankTwoJordanSumIndex j) K)
    (H : Matrix (rankTwoJordanSumIndex j) (SLInput u v) K)
    (hGH : G*H=1) (hHG : H*G=1)
    (hcong : (G.map C).transpose*glKirillovMatrix M P*G.map C=rankTwoJordanSumTarget lam j)
    (htrace : ∀ v, slInputTrace K K (G*ᵥv)=∑ i, v ⟨i,.inl (.inl 0)⟩) :
    ∃ T : Matrix (SLChartInput u v s₀) (rankTwoSLGroupedIndex j i₀) K,
    ∃ S : Matrix (rankTwoSLGroupedIndex j i₀) (SLChartInput u v s₀) K,
      T*S=1 ∧ S*T=1 ∧
      (T.map C).transpose*slKirillovMatrix M P s₀*T.map C=rankTwoSLSeparatedTarget lam j i₀ := by
  obtain ⟨U,V,hUV,hVU,hU,htraceU⟩ := rankTwoJordanSumTarget_grouped_shear lam hlam j
  have hGV : (G*U)*(V*H)=1 := by
    rw [Matrix.mul_assoc,← Matrix.mul_assoc U,hUV,Matrix.one_mul,hGH]
  have hVG : (V*H)*(G*U)=1 := by
    rw [Matrix.mul_assoc,← Matrix.mul_assoc H,hHG,Matrix.one_mul,hVU]
  let A := Matrix.fromBlocks
    (skewCrossMatrix (Matrix.fromBlocks (regularPoleDiagonal lam) (allOnesMatrix n K[X])
      0 (regularPoleDiagonal lam))) 0 0 (rankTwoJordanTailTarget lam j)
  have hGA : ((G*U).map C).transpose*glKirillovMatrix M P*(G*U).map C=A := by
    rw [Matrix.map_mul,Matrix.transpose_mul]
    calc
      _ = (U.map C).transpose*((G.map C).transpose*glKirillovMatrix M P*G.map C)*U.map C := by
        simp only [Matrix.mul_assoc]
      _ = A := by rw [hcong]; exact hU
  have htr (v : rankTwoJordanGroupedIndex j → K) :
      slInputTrace K K ((G*U)*ᵥv)=∑ i, v (.inl (.inl (.inl i))) := by
    rw [← Matrix.mulVec_mulVec,htrace,htraceU]
  obtain ⟨T,S,hTS,hST,hcongT⟩ := slTraceTransport_congruence s₀ M P A
    (G*U) (V*H) hGV hVG hGA (fun v => ∑ i, v (.inl (.inl (.inl i)))) htr
    (rankTwoSLGroupedEmbedding j i₀) (rankTwoSLGroupedRetraction j i₀)
    (rankTwoSLGroupedRetraction_embedding j i₀)
    (rankTwoSLGroupedEmbedding_trace j i₀) (rankTwoSLGroupedEmbedding_retraction j i₀)
  have htarget : (T.map C).transpose*slKirillovMatrix M P s₀*T.map C=
      Matrix.fromBlocks
        (skewCrossMatrix (Matrix.fromBlocks (poleTracePencil lam i₀) 0 0 (regularPoleDiagonal lam)))
        0 0 (rankTwoJordanTailTarget lam j) :=
    hcongT.trans (rankTwoSLGroupedEmbedding_restrict lam j i₀)
  let e := rankTwoSLPairOrder j i₀
  refine ⟨T.submatrix id e,S.submatrix e id,?_,?_,?_⟩
  · rw [Matrix.submatrix_mul_equiv,hTS,Matrix.submatrix_id_id]
  · change S.submatrix e (Equiv.refl _) * T.submatrix (Equiv.refl _) e=1
    rw [Matrix.submatrix_mul_equiv,hST]
    exact Matrix.submatrix_one_equiv e
  · simp only [← Matrix.submatrix_map]
    rw [congruence_column_reindex,htarget,rankTwoSLSeparatedTarget_reindex]

end FD56
