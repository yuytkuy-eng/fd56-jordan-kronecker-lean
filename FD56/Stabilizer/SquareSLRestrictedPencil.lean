/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.SquareSLTraceChart
import FD56.Stabilizer.SLTraceTransport

/-! Restrict the trace-preserving square GL decomposition and separate its singular part. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

def squareSLSeparatedTarget (lam : n → K) (j : n → n) (i₀ : n) :
    Matrix (squareSLGroupedIndex j i₀) (squareSLGroupedIndex j i₀) K[X] :=
  Matrix.fromBlocks
    (Matrix.fromBlocks (skewCrossMatrix (poleTracePencil lam i₀)) 0 0
      (skewCrossMatrix (regularPoleDiagonal lam))) 0 0 (squareGLTailTarget lam j)

def squareSLPairOrder (j : n → n) (i₀ : n) :
    squareSLGroupedIndex j i₀ ≃ squareSLGroupedIndex j i₀ :=
  Equiv.sumCongr (Equiv.sumSumSumComm {i : n // i≠i₀} n n n) (Equiv.refl _)

omit [Fintype n] in
theorem squareSLGroupedEmbedding_map {L : Type*} [Field L] (f : K →+* L)
    (j : n → n) (i₀ : n) :
    (squareSLGroupedEmbedding (K := K) j i₀).map f=squareSLGroupedEmbedding j i₀ := by
  have h : (poleTraceChart (K := K) i₀).map f=poleTraceChart (K := L) i₀ := by
    funext i k
    simp only [Matrix.map_apply,poleTraceChart,map_sub]
    split_ifs <;> simp
  simp only [squareSLGroupedEmbedding,Matrix.fromBlocks_map,h,
    Matrix.map_zero _ (map_zero f),Matrix.map_one _ (map_zero f) (map_one f)]

theorem squareSLGroupedEmbedding_restrict (lam : n → K) (j : n → n) (i₀ : n) :
    ((squareSLGroupedEmbedding (K := K) j i₀).map C).transpose *
        Matrix.fromBlocks (skewCrossMatrix (Matrix.fromBlocks (regularPoleDiagonal lam)
          (allOnesMatrix n K[X]) 0 (regularPoleDiagonal lam))) 0 0 (squareGLTailTarget lam j) *
        (squareSLGroupedEmbedding j i₀).map C =
      Matrix.fromBlocks
        (skewCrossMatrix (Matrix.fromBlocks (poleTracePencil lam i₀) 0 0 (regularPoleDiagonal lam)))
        0 0 (squareGLTailTarget lam j) := by
  let E : Matrix (n ⊕ n) ({i : n // i≠i₀} ⊕ n) K[X] :=
    Matrix.fromBlocks ((poleTraceChart (K := K) i₀).map C) 0 0 1
  have hE : E.transpose * Matrix.fromBlocks (regularPoleDiagonal lam) (allOnesMatrix n K[X])
      0 (regularPoleDiagonal lam)=Matrix.fromBlocks (poleTracePencil lam i₀) 0 0 (regularPoleDiagonal lam) :=
    distinctPole_hyperplane_cross lam _ (poleTraceChart_sum i₀)
  have hmap : (squareSLGroupedEmbedding (K := K) j i₀).map C=
      Matrix.fromBlocks (Matrix.fromBlocks E 0 0 1) 0 0 1 := by
    simp only [squareSLGroupedEmbedding,Matrix.fromBlocks_map,E,
      Matrix.map_zero _ (map_zero C),Matrix.map_one _ (map_zero C) (map_one C)]
  rw [hmap]
  simp only [Matrix.fromBlocks_transpose,Matrix.transpose_zero,Matrix.transpose_one,
    Matrix.fromBlocks_multiply,Matrix.mul_zero,Matrix.zero_mul,zero_add,add_zero,
    Matrix.one_mul,Matrix.mul_one]
  have hcore := skewCross_restrict_first E
    (Matrix.fromBlocks (regularPoleDiagonal lam) (allOnesMatrix n K[X]) 0 (regularPoleDiagonal lam))
  rw [hE] at hcore
  simpa only [Matrix.fromBlocks_transpose,Matrix.transpose_zero,Matrix.transpose_one] using
    congrArg (fun Z => Matrix.fromBlocks Z 0 0 (squareGLTailTarget lam j)) hcore

theorem squareSLSeparatedTarget_reindex (lam : n → K) (j : n → n) (i₀ : n) :
    (Matrix.fromBlocks
      (skewCrossMatrix (Matrix.fromBlocks (poleTracePencil lam i₀) 0 0 (regularPoleDiagonal lam)))
      0 0 (squareGLTailTarget lam j)).submatrix (squareSLPairOrder j i₀) (squareSLPairOrder j i₀) =
      squareSLSeparatedTarget lam j i₀ := by
  funext u v
  rcases u with ((i|i)|(i|i))|i <;> rcases v with ((k|k)|(k|k))|k <;>
    simp [squareSLSeparatedTarget,squareSLPairOrder,Equiv.sumSumSumComm,skewCrossMatrix]

theorem squareSL_restriction_of_traced_jordan (M P : Matrix n n K[X])
    (lam : n → K) (hlam : Function.Injective lam) (j : n → n) (i₀ : n)
    (G : Matrix (SLInput n n) (squareGLJordanIndex j) K)
    (H : Matrix (squareGLJordanIndex j) (SLInput n n) K)
    (hGH : G*H=1) (hHG : H*G=1)
    (hcong : (G.map C).transpose*glKirillovMatrix M P*G.map C=squareGLJordanTarget lam j)
    (htrace : ∀ v, slInputTrace K K (G*ᵥv)=∑ i, v ⟨i,.inl (.inl 0)⟩) :
    ∃ T : Matrix (SLChartInput n n i₀) (squareSLGroupedIndex j i₀) K,
    ∃ S : Matrix (squareSLGroupedIndex j i₀) (SLChartInput n n i₀) K,
      T*S=1 ∧ S*T=1 ∧
      (T.map C).transpose*slKirillovMatrix M P i₀*T.map C=squareSLSeparatedTarget lam j i₀ := by
  obtain ⟨U,V,hUV,hVU,hU,htraceU⟩ := squareGLJordanTarget_grouped_shear lam hlam j
  have hGV : (G*U)*(V*H)=1 := by
    rw [Matrix.mul_assoc,← Matrix.mul_assoc U,hUV,Matrix.one_mul,hGH]
  have hVG : (V*H)*(G*U)=1 := by
    rw [Matrix.mul_assoc,← Matrix.mul_assoc H,hHG,Matrix.one_mul,hVU]
  let A := Matrix.fromBlocks
    (skewCrossMatrix (Matrix.fromBlocks (regularPoleDiagonal lam) (allOnesMatrix n K[X])
      0 (regularPoleDiagonal lam))) 0 0 (squareGLTailTarget lam j)
  have hGA : ((G*U).map C).transpose*glKirillovMatrix M P*(G*U).map C=A := by
    rw [Matrix.map_mul,Matrix.transpose_mul]
    calc
      _ = (U.map C).transpose*((G.map C).transpose*glKirillovMatrix M P*G.map C)*U.map C := by
        simp only [Matrix.mul_assoc]
      _ = A := by rw [hcong]; exact hU
  have htr (v : squareGLGroupedIndex j → K) :
      slInputTrace K K ((G*U)*ᵥv)=∑ i, v (.inl (.inl (.inl i))) := by
    rw [← Matrix.mulVec_mulVec,htrace,htraceU]
  obtain ⟨T,S,hTS,hST,hcongT⟩ := slTraceTransport_congruence i₀ M P A
    (G*U) (V*H) hGV hVG hGA (fun v => ∑ i, v (.inl (.inl (.inl i)))) htr
    (squareSLGroupedEmbedding j i₀) (squareSLGroupedRetraction j i₀)
    (squareSLGroupedRetraction_embedding j i₀)
    (squareSLGroupedEmbedding_trace j i₀) (squareSLGroupedEmbedding_retraction j i₀)
  have htarget : (T.map C).transpose*slKirillovMatrix M P i₀*T.map C=
      Matrix.fromBlocks
        (skewCrossMatrix (Matrix.fromBlocks (poleTracePencil lam i₀) 0 0 (regularPoleDiagonal lam)))
        0 0 (squareGLTailTarget lam j) :=
    hcongT.trans (squareSLGroupedEmbedding_restrict lam j i₀)
  let e := squareSLPairOrder j i₀
  refine ⟨T.submatrix id e,S.submatrix e id,?_,?_,?_⟩
  · rw [Matrix.submatrix_mul_equiv,hTS,Matrix.submatrix_id_id]
  · change S.submatrix e (Equiv.refl _) * T.submatrix (Equiv.refl _) e=1
    rw [Matrix.submatrix_mul_equiv,hST]
    exact Matrix.submatrix_one_equiv e
  · simp only [← Matrix.submatrix_map]
    rw [congruence_column_reindex,htarget,squareSLSeparatedTarget_reindex]

theorem squareSL_normalized_separated_decomposition (A B P₀ P₁ V S T : Matrix n n K)
    (hST : S*T=1) (hTS : T*S=1) (hP₁V : P₁*V=1) (hVP₁ : V*P₁=1)
    (lam : n → K) (hlam : Function.Injective lam)
    (hdiag : (-V*P₀)*S=S*Matrix.diagonal lam)
    (j : n → n) (hj : ∀ i, i≠j i)
    (hres : ∀ i, (T*A*S) (j i) i+lam i*(T*B*S) (j i) i≠0) (i₀ : n) :
    ∃ G : Matrix (SLChartInput n n i₀) (squareSLGroupedIndex j i₀) K,
    ∃ H : Matrix (squareSLGroupedIndex j i₀) (SLChartInput n n i₀) K,
      G*H=1 ∧ H*G=1 ∧
      (G.map C).transpose*slKirillovMatrix (affineMatrixPencil A B)
        (affineMatrixPencil P₀ P₁) i₀*G.map C=squareSLSeparatedTarget lam j i₀ := by
  obtain ⟨G,H,hGH,hHG,hcong,htrace⟩ := squareGL_normalized_jordan_trace_decomposition
    A B P₀ P₁ V S T hST hTS hP₁V hVP₁ lam hlam hdiag j hj hres
  exact squareSL_restriction_of_traced_jordan _ _ lam hlam j i₀ G H hGH hHG hcong htrace

end FD56
