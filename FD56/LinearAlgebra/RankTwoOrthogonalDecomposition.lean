/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.AlternatingRankTwoPairing
import FD56.LinearAlgebra.OrthogonalColumnSplit
import FD56.LinearAlgebra.SymplecticMatrixNormalization

/-! Isolate a prescribed nondegenerate block containing the image of a rank-two form. -/

noncomputable section
namespace FD56
open Matrix

theorem rank_two_alternating_pair_decomposition {K n a : Type*} [Field K]
    [Fintype n] [Fintype a] [DecidableEq n] [DecidableEq a]
    (A B N : Matrix n n K) (Q : Matrix n a K)
    (hNA : N.transpose*B=A)
    (hA : ∀ w : n → K, w ⬝ᵥ (A *ᵥ w)=0)
    (hB : ∀ w : n → K, w ⬝ᵥ (B *ᵥ w)=0)
    (hr : Module.finrank K (LinearMap.range (Matrix.toLin' A))≤2)
    (hdet : B.det≠0) (hG : (Q.transpose*B*Q).det≠0)
    (u v : n → K) (hc : u ⬝ᵥ (A *ᵥ v)≠0)
    (i j : a) (hu : (fun k => Q k i)=N *ᵥ u) (hv : (fun k => Q k j)=N *ᵥ v) :
    ∃ k : ℕ, Fintype.card n-Fintype.card a=2*k ∧
    ∃ S : Matrix n (a ⊕ (Fin 2 × Fin k)) K,
    ∃ T : Matrix (a ⊕ (Fin 2 × Fin k)) n K,
      S*T=1 ∧ T*S=1 ∧ S.submatrix id Sum.inl=Q ∧
      S.transpose*A*S=Matrix.fromBlocks (Q.transpose*A*Q) 0 0 0 ∧
      S.transpose*B*S=Matrix.fromBlocks (Q.transpose*B*Q) 0 0 (standardSymplecticMatrix K k) := by
  obtain ⟨S,T,D,hST,hTS,hSQ,hcross,hBsplit,hD,hDdet⟩ :=
    alternating_orthogonal_column_split B Q hB hdet hG
  let R := S.submatrix id Sum.inr
  have hAR : A*R=0 := alternating_rank_two_orthogonal_columns A B N Q R
    hNA hA hr u v hc i j hu hv hcross
  have hRA : R.transpose*A=0 := by
    have hh := congrArg Matrix.transpose hAR
    rw [Matrix.transpose_mul,alternating_matrix_transpose A hA,
      Matrix.mul_neg,Matrix.transpose_zero] at hh
    exact neg_eq_zero.mp hh
  have hS : S=Matrix.fromCols Q R := by
    rw [← hSQ]
    exact (Matrix.fromCols_toCols S).symm
  have hAsplit : S.transpose*A*S=Matrix.fromBlocks (Q.transpose*A*Q) 0 0 0 := by
    rw [hS,Matrix.transpose_fromCols,Matrix.fromRows_mul,Matrix.fromRows_mul_fromCols]
    simp only [Matrix.mul_assoc,hAR,hRA,Matrix.mul_zero,Matrix.zero_mul]
  obtain ⟨k,hk,V,W,hVW,hWV,hVD⟩ := alternating_nondegenerate_symplectic_normalization D hD hDdet
  let F : Matrix (a ⊕ Fin (Fintype.card n-Fintype.card a)) (a ⊕ (Fin 2 × Fin k)) K :=
    Matrix.fromBlocks 1 0 0 V
  let G : Matrix (a ⊕ (Fin 2 × Fin k)) (a ⊕ Fin (Fintype.card n-Fintype.card a)) K :=
    Matrix.fromBlocks 1 0 0 W
  have hFG : F*G=1 := by simp [F,G,Matrix.fromBlocks_multiply,hVW,Matrix.fromBlocks_one]
  have hGF : G*F=1 := by simp [F,G,Matrix.fromBlocks_multiply,hWV,Matrix.fromBlocks_one]
  refine ⟨k,by simpa only [Fintype.card_fin] using hk,S*F,G*T,?_,?_,?_,?_,?_⟩
  · rw [Matrix.mul_assoc,← Matrix.mul_assoc F,hFG,Matrix.one_mul,hST]
  · rw [Matrix.mul_assoc,← Matrix.mul_assoc T,hTS,Matrix.one_mul,hGF]
  · rw [hS]
    change (Matrix.fromCols Q R * Matrix.fromBlocks 1 0 0 V).submatrix id Sum.inl=Q
    rw [Matrix.fromCols_mul_fromBlocks]
    simp only [Matrix.mul_one,Matrix.mul_zero,add_zero,zero_add]
    rfl
  · rw [Matrix.transpose_mul]
    calc
      _ = F.transpose*(S.transpose*A*S)*F := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [hAsplit]
        simp only [F,Matrix.fromBlocks_transpose,Matrix.transpose_zero,Matrix.transpose_one,
          Matrix.fromBlocks_multiply,Matrix.mul_zero,Matrix.zero_mul,zero_add,add_zero,
          Matrix.one_mul,Matrix.mul_one]
  · rw [Matrix.transpose_mul]
    calc
      _ = F.transpose*(S.transpose*B*S)*F := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [hBsplit]
        simp only [F,Matrix.fromBlocks_transpose,Matrix.transpose_zero,Matrix.transpose_one,
          Matrix.fromBlocks_multiply,Matrix.mul_zero,Matrix.zero_mul,zero_add,add_zero,
          Matrix.one_mul,Matrix.mul_one,hVD]

end FD56
