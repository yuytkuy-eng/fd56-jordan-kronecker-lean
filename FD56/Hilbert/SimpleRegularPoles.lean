/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.SquareSLCanonicalTarget

/-! An alternating coupling over distinct simple poles has only two-dimensional regular blocks. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

omit [Fintype n] in
theorem simple_pole_residual_zero (lam : n → K) (hlam : Function.Injective lam)
    (A B : Matrix n n K) (hAd : ∀ i, A i i = 0) (hBd : ∀ i, B i i = 0) :
    regularPoleResidual lam A B = 0 := by
  funext i j
  by_cases h : i = j
  · subst j
    simp [regularPoleResidual, hAd, hBd]
  · simp [regularPoleResidual, hlam.ne h]

theorem simple_regular_pole_decomposition (lam : n → K) (hlam : Function.Injective lam)
    (A B : Matrix n n K) (hA : A.transpose = -A) (hB : B.transpose = -B)
    (hAd : ∀ i, A i i = 0) (hBd : ∀ i, B i i = 0) :
    ∃ T : Matrix (n ⊕ n) ((Fin 1 ⊕ Fin 1) × n) K,
    ∃ S : Matrix ((Fin 1 ⊕ Fin 1) × n) (n ⊕ n) K,
      T * S = 1 ∧ S * T = 1 ∧
      (T.map C).transpose * regularPolePencil lam A B * T.map C =
        Matrix.blockDiagonal (fun i => skewJordanBlockPencil (lam i) 1) := by
  letI : LinearOrder n := LinearOrder.lift' (Fintype.equivFin n) (Fintype.equivFin n).injective
  obtain ⟨T,S,hTS,hST,hcong⟩ := regular_pole_constant_separation lam A B hA hB hBd
  rw [simple_pole_residual_zero lam hlam A B hAd hBd, Matrix.map_zero _ (map_zero C)] at hcong
  have htarget : Matrix.fromBlocks (0 : Matrix n n K[X]) (regularPoleDiagonal lam)
      (-regularPoleDiagonal lam) 0 = skewCrossMatrix (regularPoleDiagonal lam) := by
    simp only [skewCrossMatrix, regularPoleDiagonal, Matrix.diagonal_transpose]
  rw [htarget] at hcong
  let e := simplePoleIndex n
  refine ⟨T.submatrix id e, S.submatrix e id, ?_, ?_, ?_⟩
  · rw [Matrix.submatrix_mul_equiv, hTS, Matrix.submatrix_id_id]
  · change S.submatrix e (Equiv.refl _) * T.submatrix (Equiv.refl _) e = 1
    rw [Matrix.submatrix_mul_equiv, hST]
    exact Matrix.submatrix_one_equiv e
  · simp only [← Matrix.submatrix_map]
    rw [congruence_column_reindex, hcong]
    exact regularPoleDiagonal_simple_blocks lam

end FD56
