/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.SquareSLRestrictedPencil
import FD56.Hilbert.DistinctPoleKronecker
import FD56.Hilbert.SingleKroneckerBlock

/-! The separated square SL pencil consists of one singular block and simple regular blocks. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

def simplePoleIndex (n : Type*) : ((Fin 1 ⊕ Fin 1) × n) ≃ (n ⊕ n) where
  toFun
    | (.inl _,i) => .inl i
    | (.inr _,i) => .inr i
  invFun
    | .inl i => (.inl 0,i)
    | .inr i => (.inr 0,i)
  left_inv x := by rcases x with ⟨k|k,i⟩ <;> fin_cases k <;> rfl
  right_inv x := by cases x <;> rfl

omit [Fintype n] in
theorem regularPoleDiagonal_simple_blocks (lam : n → K) :
    (skewCrossMatrix (regularPoleDiagonal lam)).submatrix (simplePoleIndex n) (simplePoleIndex n)=
      Matrix.blockDiagonal (fun i => skewJordanBlockPencil (lam i) 1) := by
  funext u v
  rcases u with ⟨a|a,i⟩ <;> rcases v with ⟨b|b,k⟩ <;> fin_cases a <;> fin_cases b <;>
    by_cases hik : i=k
  all_goals try subst k
  all_goals simp_all [simplePoleIndex,skewCrossMatrix,regularPoleDiagonal,Matrix.diagonal,
    Matrix.blockDiagonal,skewJordanBlockPencil,jordanUpperPencil]
  all_goals aesop

abbrev squareSLCanonicalIndex (j : n → n) :=
  (((Fin (Fintype.card n-1) ⊕ Fin (Fintype.card n-1+1)) ⊕ ((Fin 1 ⊕ Fin 1) × n)) ⊕ squareGLTailIndex j)

def squareSLCanonicalTarget (lam : n → K) (j : n → n) :
    Matrix (squareSLCanonicalIndex j) (squareSLCanonicalIndex j) K[X] :=
  Matrix.fromBlocks
    (Matrix.fromBlocks (kroneckerBlockPencil (Fintype.card n-1)) 0 0
      (Matrix.blockDiagonal (fun i => skewJordanBlockPencil (lam i) 1)))
    0 0 (squareGLTailTarget lam j)

theorem squareSLSeparatedTarget_canonical [Nontrivial n] (lam : n → K)
    (hlam : Function.Injective lam) (j : n → n) (i₀ : n) :
    ∃ T : Matrix (squareSLGroupedIndex j i₀) (squareSLCanonicalIndex j) K,
    ∃ S : Matrix (squareSLCanonicalIndex j) (squareSLGroupedIndex j i₀) K,
      T*S=1 ∧ S*T=1 ∧
      (T.map C).transpose*squareSLSeparatedTarget lam j i₀*T.map C=squareSLCanonicalTarget lam j := by
  obtain ⟨U,V,hUV,hVU,hcong⟩ := single_kronecker_block_congruence
    (skewCrossMatrix (poleTracePencil lam i₀)) (Fintype.card n-1)
    (poleTraceSkew_kronecker_decomposition lam hlam i₀)
  let b := Fin (Fintype.card n-1) ⊕ Fin (Fintype.card n-1+1)
  let P : Matrix (squareSLGroupedIndex j i₀) ((b ⊕ (n ⊕ n)) ⊕ squareGLTailIndex j) K :=
    Matrix.fromBlocks (Matrix.fromBlocks U 0 0 1) 0 0 1
  let Q : Matrix ((b ⊕ (n ⊕ n)) ⊕ squareGLTailIndex j) (squareSLGroupedIndex j i₀) K :=
    Matrix.fromBlocks (Matrix.fromBlocks V 0 0 1) 0 0 1
  have hPQ : P*Q=1 := by simp [P,Q,Matrix.fromBlocks_multiply,hUV,Matrix.fromBlocks_one]
  have hQP : Q*P=1 := by simp [P,Q,Matrix.fromBlocks_multiply,hVU,Matrix.fromBlocks_one]
  have hP : (P.map C).transpose*squareSLSeparatedTarget lam j i₀*P.map C=
      Matrix.fromBlocks (Matrix.fromBlocks (kroneckerBlockPencil (Fintype.card n-1)) 0 0
        (skewCrossMatrix (regularPoleDiagonal lam))) 0 0 (squareGLTailTarget lam j) := by
    simp only [P,squareSLSeparatedTarget,Matrix.fromBlocks_map,
      Matrix.map_zero _ (map_zero C),Matrix.map_one _ (map_zero C) (map_one C),
      Matrix.fromBlocks_transpose,Matrix.transpose_zero,Matrix.transpose_one,Matrix.fromBlocks_multiply,
      Matrix.mul_zero,Matrix.zero_mul,zero_add,add_zero,Matrix.one_mul,Matrix.mul_one,hcong]
  let e : squareSLCanonicalIndex j ≃ ((b ⊕ (n ⊕ n)) ⊕ squareGLTailIndex j) :=
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

theorem squareSLCanonical_regular_count [Nontrivial n] (i k : n) (hik : i≠k) :
    Fintype.card (Unit ⊕ {j : n // j≠i ∧ j≠k})=Fintype.card n-1 := by
  have hn : 2≤Fintype.card n := Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
  rw [Fintype.card_sum,Fintype.card_unique,twoPivot_complement_card i k hik]
  omega

theorem squareSL_canonical_of_separated [Nontrivial n] (M P : Matrix n n K[X])
    (lam : n → K) (hlam : Function.Injective lam) (j : n → n) (i₀ : n)
    (G : Matrix (SLChartInput n n i₀) (squareSLGroupedIndex j i₀) K)
    (H : Matrix (squareSLGroupedIndex j i₀) (SLChartInput n n i₀) K)
    (hGH : G*H=1) (hHG : H*G=1)
    (hcong : (G.map C).transpose*slKirillovMatrix M P i₀*G.map C=squareSLSeparatedTarget lam j i₀) :
    ∃ T : Matrix (SLChartInput n n i₀) (squareSLCanonicalIndex j) K,
    ∃ S : Matrix (squareSLCanonicalIndex j) (SLChartInput n n i₀) K,
      T*S=1 ∧ S*T=1 ∧
      (T.map C).transpose*slKirillovMatrix M P i₀*T.map C=squareSLCanonicalTarget lam j := by
  obtain ⟨U,V,hUV,hVU,hU⟩ := squareSLSeparatedTarget_canonical lam hlam j i₀
  refine ⟨G*U,V*H,?_,?_,?_⟩
  · rw [Matrix.mul_assoc,← Matrix.mul_assoc U,hUV,Matrix.one_mul,hGH]
  · rw [Matrix.mul_assoc,← Matrix.mul_assoc H,hHG,Matrix.one_mul,hVU]
  · rw [Matrix.map_mul,Matrix.transpose_mul]
    calc
      _ = (U.map C).transpose*((G.map C).transpose*slKirillovMatrix M P i₀*G.map C)*U.map C := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hcong,hU]

end FD56
