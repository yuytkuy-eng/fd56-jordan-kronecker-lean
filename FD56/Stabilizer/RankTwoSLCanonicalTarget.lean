/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.RankTwoSLRestrictedPencil
import FD56.Stabilizer.SquareSLCanonicalTarget
import FD56.Hilbert.DistinctPoleKronecker
import FD56.Hilbert.SingleKroneckerBlock

/-! Canonical form of a trace-normalized Jordan sum with arbitrary simple tails. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

abbrev rankTwoSLCanonicalIndex (j : n → ℕ) :=
  (((Fin (Fintype.card n-1) ⊕ Fin (Fintype.card n-1+1)) ⊕ ((Fin 1 ⊕ Fin 1) × n)) ⊕ rankTwoJordanTailIndex j)

def rankTwoSLCanonicalTarget (lam : n → K) (j : n → ℕ) :
    Matrix (rankTwoSLCanonicalIndex j) (rankTwoSLCanonicalIndex j) K[X] :=
  Matrix.fromBlocks
    (Matrix.fromBlocks (kroneckerBlockPencil (Fintype.card n-1)) 0 0
      (Matrix.blockDiagonal (fun i => skewJordanBlockPencil (lam i) 1)))
    0 0 (rankTwoJordanTailTarget lam j)

theorem rankTwoSLSeparatedTarget_canonical [Nontrivial n] (lam : n → K)
    (hlam : Function.Injective lam) (j : n → ℕ) (i₀ : n) :
    ∃ T : Matrix (rankTwoSLGroupedIndex j i₀) (rankTwoSLCanonicalIndex j) K,
    ∃ S : Matrix (rankTwoSLCanonicalIndex j) (rankTwoSLGroupedIndex j i₀) K,
      T*S=1 ∧ S*T=1 ∧
      (T.map C).transpose*rankTwoSLSeparatedTarget lam j i₀*T.map C=rankTwoSLCanonicalTarget lam j := by
  obtain ⟨U,V,hUV,hVU,hcong⟩ := single_kronecker_block_congruence
    (skewCrossMatrix (poleTracePencil lam i₀)) (Fintype.card n-1)
    (poleTraceSkew_kronecker_decomposition lam hlam i₀)
  let b := Fin (Fintype.card n-1) ⊕ Fin (Fintype.card n-1+1)
  let P : Matrix (rankTwoSLGroupedIndex j i₀) ((b ⊕ (n ⊕ n)) ⊕ rankTwoJordanTailIndex j) K :=
    Matrix.fromBlocks (Matrix.fromBlocks U 0 0 1) 0 0 1
  let Q : Matrix ((b ⊕ (n ⊕ n)) ⊕ rankTwoJordanTailIndex j) (rankTwoSLGroupedIndex j i₀) K :=
    Matrix.fromBlocks (Matrix.fromBlocks V 0 0 1) 0 0 1
  have hPQ : P*Q=1 := by simp [P,Q,Matrix.fromBlocks_multiply,hUV,Matrix.fromBlocks_one]
  have hQP : Q*P=1 := by simp [P,Q,Matrix.fromBlocks_multiply,hVU,Matrix.fromBlocks_one]
  have hP : (P.map C).transpose*rankTwoSLSeparatedTarget lam j i₀*P.map C=
      Matrix.fromBlocks (Matrix.fromBlocks (kroneckerBlockPencil (Fintype.card n-1)) 0 0
        (skewCrossMatrix (regularPoleDiagonal lam))) 0 0 (rankTwoJordanTailTarget lam j) := by
    simp only [P,rankTwoSLSeparatedTarget,Matrix.fromBlocks_map,
      Matrix.map_zero _ (map_zero C),Matrix.map_one _ (map_zero C) (map_one C),
      Matrix.fromBlocks_transpose,Matrix.transpose_zero,Matrix.transpose_one,Matrix.fromBlocks_multiply,
      Matrix.mul_zero,Matrix.zero_mul,zero_add,add_zero,Matrix.one_mul,Matrix.mul_one,hcong]
  let e : rankTwoSLCanonicalIndex j ≃ ((b ⊕ (n ⊕ n)) ⊕ rankTwoJordanTailIndex j) :=
    Equiv.sumCongr (Equiv.sumCongr (Equiv.refl b) (simplePoleIndex n)) (Equiv.refl _)
  refine ⟨P.submatrix id e,Q.submatrix e id,?_,?_,?_⟩
  · rw [Matrix.submatrix_mul_equiv,hPQ,Matrix.submatrix_id_id]
  · change Q.submatrix e (Equiv.refl _) * P.submatrix (Equiv.refl _) e=1
    rw [Matrix.submatrix_mul_equiv,hQP]
    exact Matrix.submatrix_one_equiv e
  · simp only [← Matrix.submatrix_map]
    rw [congruence_column_reindex,hP]
    have hsimple := regularPoleDiagonal_simple_blocks lam
    funext u v
    rcases u with (u|u)|u <;> rcases v with (v|v)|v
    all_goals try rfl
    exact congrFun (congrFun hsimple u) v

theorem rankTwoSL_canonical_of_separated [Nontrivial n]
    {u v : Type*} [Fintype u] [Fintype v] [DecidableEq u] [DecidableEq v]
    (M : Matrix u u K[X]) (P : Matrix v u K[X]) (s₀ : u)
    (lam : n → K) (hlam : Function.Injective lam) (j : n → ℕ) (i₀ : n)
    (G : Matrix (SLChartInput u v s₀) (rankTwoSLGroupedIndex j i₀) K)
    (H : Matrix (rankTwoSLGroupedIndex j i₀) (SLChartInput u v s₀) K)
    (hGH : G*H=1) (hHG : H*G=1)
    (hcong : (G.map C).transpose*slKirillovMatrix M P s₀*G.map C=rankTwoSLSeparatedTarget lam j i₀) :
    ∃ T : Matrix (SLChartInput u v s₀) (rankTwoSLCanonicalIndex j) K,
    ∃ S : Matrix (rankTwoSLCanonicalIndex j) (SLChartInput u v s₀) K,
      T*S=1 ∧ S*T=1 ∧
      (T.map C).transpose*slKirillovMatrix M P s₀*T.map C=rankTwoSLCanonicalTarget lam j := by
  obtain ⟨U,V,hUV,hVU,hU⟩ := rankTwoSLSeparatedTarget_canonical lam hlam j i₀
  refine ⟨G*U,V*H,?_,?_,?_⟩
  · rw [Matrix.mul_assoc,← Matrix.mul_assoc U,hUV,Matrix.one_mul,hGH]
  · rw [Matrix.mul_assoc,← Matrix.mul_assoc H,hHG,Matrix.one_mul,hVU]
  · rw [Matrix.map_mul,Matrix.transpose_mul]
    calc
      _ = (U.map C).transpose*((G.map C).transpose*slKirillovMatrix M P s₀*G.map C)*U.map C := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hcong,hU]

end FD56
