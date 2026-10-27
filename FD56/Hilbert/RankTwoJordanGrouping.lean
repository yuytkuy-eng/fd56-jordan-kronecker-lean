/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.SquareGLTracedJordan
import FD56.Hilbert.NilpotentRankTwoJordan
import FD56.Hilbert.DistinctPoleHyperplane

/-! Group arbitrary rank-two Jordan sums before restricting their trace functional. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

abbrev rankTwoJordanSumIndex (j : n → ℕ) := Σ i : n, rankTwoJordanIndex (j i)

def rankTwoJordanSumTarget (lam : n → K) (j : n → ℕ) :
    Matrix (rankTwoJordanSumIndex j) (rankTwoJordanSumIndex j) K[X] :=
  Matrix.blockDiagonal' (fun i => rankTwoJordanPencil (lam i) (j i))

abbrev rankTwoJordanTailIndex (j : n → ℕ) :=
  Σ i : n, (Fin 1 ⊕ Fin 1) × Fin (j i)

abbrev rankTwoJordanGroupedIndex (j : n → ℕ) :=
  ((n ⊕ n) ⊕ (n ⊕ n)) ⊕ rankTwoJordanTailIndex j

def rankTwoJordanGroup (j : n → ℕ) : rankTwoJordanGroupedIndex j ≃ rankTwoJordanSumIndex j where
  toFun
    | .inl (.inl (.inl i)) => ⟨i,.inl (.inl 0)⟩
    | .inl (.inl (.inr i)) => ⟨i,.inl (.inl 1)⟩
    | .inl (.inr (.inl i)) => ⟨i,.inl (.inr 0)⟩
    | .inl (.inr (.inr i)) => ⟨i,.inl (.inr 1)⟩
    | .inr ⟨i,k⟩ => ⟨i,.inr k⟩
  invFun
    | ⟨i,.inl (.inl k)⟩ => if k=0 then .inl (.inl (.inl i)) else .inl (.inl (.inr i))
    | ⟨i,.inl (.inr k)⟩ => if k=0 then .inl (.inr (.inl i)) else .inl (.inr (.inr i))
    | ⟨i,.inr k⟩ => .inr ⟨i,k⟩
  left_inv x := by
    rcases x with ((i|i)|(i|i))|⟨i,k⟩ <;> simp
  right_inv x := by
    rcases x with ⟨i,(k|k)|k⟩
    · fin_cases k <;> simp
    · fin_cases k <;> simp
    · rfl

def rankTwoJordanTailTarget (lam : n → K) (j : n → ℕ) :
    Matrix (rankTwoJordanTailIndex j) (rankTwoJordanTailIndex j) K[X] :=
  Matrix.blockDiagonal' (fun i => Matrix.blockDiagonal
    (fun _ : Fin (j i) => skewJordanBlockPencil (lam i) 1))

omit [Fintype n] in
theorem rankTwoJordanSumTarget_group (lam : n → K) (j : n → ℕ) :
    (rankTwoJordanSumTarget lam j).submatrix (rankTwoJordanGroup j) (rankTwoJordanGroup j) =
      Matrix.fromBlocks
        (skewCrossMatrix (Matrix.fromBlocks (regularPoleDiagonal lam) 1 0 (regularPoleDiagonal lam)))
        0 0 (rankTwoJordanTailTarget lam j) := by
  funext u v
  rcases u with ((i|i)|(i|i))|⟨i,a⟩ <;>
    rcases v with ((k|k)|(k|k))|⟨k,b⟩ <;>
    by_cases hik : i=k
  all_goals try subst k
  all_goals simp_all [Matrix.submatrix_apply,rankTwoJordanGroup,rankTwoJordanSumTarget,
    rankTwoJordanTailTarget,Matrix.blockDiagonal'_apply_eq,Matrix.blockDiagonal'_apply_ne,
    rankTwoJordanPencil,skewJordanBlockPencil,jordanUpperPencil,skewCrossMatrix,
    regularPoleDiagonal,Matrix.diagonal,Matrix.one_apply]
  all_goals aesop

omit [DecidableEq n] in
theorem rankTwoJordanGroup_trace (j : n → ℕ) (v : rankTwoJordanGroupedIndex j → K) :
    ∑ i, v ((rankTwoJordanGroup j).symm ⟨i,.inl (.inl 0)⟩) =
      ∑ i, v (.inl (.inl (.inl i))) := by
  rfl

theorem rankTwoJordanSumTarget_grouped_shear (lam : n → K) (hlam : Function.Injective lam)
    (j : n → ℕ) :
    ∃ T : Matrix (rankTwoJordanSumIndex j) (rankTwoJordanGroupedIndex j) K,
    ∃ S : Matrix (rankTwoJordanGroupedIndex j) (rankTwoJordanSumIndex j) K,
      T*S=1 ∧ S*T=1 ∧
      (T.map C).transpose * rankTwoJordanSumTarget lam j * T.map C =
        Matrix.fromBlocks
          (skewCrossMatrix (Matrix.fromBlocks (regularPoleDiagonal lam) (allOnesMatrix n K[X])
            0 (regularPoleDiagonal lam))) 0 0 (rankTwoJordanTailTarget lam j) ∧
      (∀ v : rankTwoJordanGroupedIndex j → K,
        ∑ i, (T*ᵥv) ⟨i,.inl (.inl 0)⟩ = ∑ i, v (.inl (.inl (.inl i)))) := by
  obtain ⟨U,V,hUV,hVU,hcong,htrace⟩ := distinctPole_alternating_constant_shear lam hlam
  let e := rankTwoJordanGroup j
  let P : Matrix (rankTwoJordanGroupedIndex j) (rankTwoJordanGroupedIndex j) K :=
    Matrix.fromBlocks U 0 0 1
  let Q : Matrix (rankTwoJordanGroupedIndex j) (rankTwoJordanGroupedIndex j) K :=
    Matrix.fromBlocks V 0 0 1
  have hPQ : P*Q=1 := by
    simp [P,Q,Matrix.fromBlocks_multiply,hUV,Matrix.fromBlocks_one]
  have hQP : Q*P=1 := by
    simp [P,Q,Matrix.fromBlocks_multiply,hVU,Matrix.fromBlocks_one]
  refine ⟨P.submatrix e.symm id,Q.submatrix id e.symm,?_,?_,?_,?_⟩
  · change P.submatrix e.symm (Equiv.refl _) * Q.submatrix (Equiv.refl _) e.symm=1
    rw [Matrix.submatrix_mul_equiv,hPQ]
    exact Matrix.submatrix_one_equiv e.symm
  · rw [Matrix.submatrix_mul_equiv,hQP,Matrix.submatrix_id_id]
  · simp only [← Matrix.submatrix_map]
    rw [congruence_row_reindex, rankTwoJordanSumTarget_group]
    simp only [P,Matrix.fromBlocks_map,Matrix.map_zero _ (map_zero C),
      Matrix.map_one _ (map_zero C) (map_one C),Matrix.fromBlocks_transpose,
      Matrix.transpose_zero,Matrix.transpose_one,Matrix.fromBlocks_multiply,
      Matrix.mul_zero,Matrix.zero_mul,zero_add,add_zero,Matrix.one_mul,Matrix.mul_one,hcong]
  · intro v
    apply Finset.sum_congr rfl
    intro i _
    change (P*ᵥv) (.inl (.inl (.inl i))) = v (.inl (.inl (.inl i)))
    simpa only [P,Matrix.fromBlocks_mulVec,Matrix.zero_mulVec,add_zero,Sum.elim_inl]
      using htrace (fun k => v (.inl k)) i

end FD56
