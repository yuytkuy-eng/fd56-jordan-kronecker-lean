/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.RegularPoleSeparation
import Mathlib.Logic.Equiv.Prod

/-! Grouping separated poles gives a literal direct sum of regular coupled blocks. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K m p : Type*} [Field K] [Fintype m] [Fintype p]
  [DecidableEq m] [DecidableEq p] [LinearOrder (m × p)]

def regularLocalCoupling (lam : p → K) (A B : Matrix (m × p) (m × p) K) (a : p) :
    Matrix m m K := fun i j => A (i,a) (j,a)+lam a*B (i,a) (j,a)

def regularLocalPolePencil (lam : p → K) (A B : Matrix (m × p) (m × p) K) (a : p) :
    Matrix (m ⊕ m) (m ⊕ m) K[X] :=
  Matrix.fromBlocks ((regularLocalCoupling lam A B a).map C)
    ((X-C (lam a)) • (1 : Matrix m m K[X]))
    (-((X-C (lam a)) • (1 : Matrix m m K[X]))) 0

omit [Fintype m] [Fintype p] [LinearOrder (m × p)] in
theorem separated_poles_reindex (lam : p → K) (hlam : Function.Injective lam)
    (A B : Matrix (m × p) (m × p) K) :
    (Matrix.fromBlocks ((regularPoleResidual (fun i : m × p => lam i.2) A B).map C)
      (regularPoleDiagonal (fun i : m × p => lam i.2))
      (-(regularPoleDiagonal (fun i : m × p => lam i.2))) 0).submatrix
        (Equiv.sumProdDistrib m m p) (Equiv.sumProdDistrib m m p) =
      Matrix.blockDiagonal (regularLocalPolePencil lam A B) := by
  classical
  funext ⟨i,a⟩ ⟨j,b⟩
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      by_cases h : a=b
      · subst b
        simp [Matrix.submatrix_apply,regularPoleResidual,regularLocalPolePencil,
          regularLocalCoupling,Matrix.blockDiagonal_apply]
      · simp [Matrix.submatrix_apply,regularPoleResidual,regularLocalPolePencil,
          Matrix.blockDiagonal_apply,h,hlam.ne h]
    | inr j =>
      by_cases h : a=b
      · subst b
        simp [Matrix.submatrix_apply,regularPoleDiagonal,regularLocalPolePencil,
          Matrix.blockDiagonal_apply,Matrix.diagonal_apply,Matrix.one_apply]
      · simp [Matrix.submatrix_apply,regularPoleDiagonal,regularLocalPolePencil,
          Matrix.blockDiagonal_apply,Matrix.diagonal_apply,h]
  | inr i =>
    cases j with
    | inl j =>
      by_cases h : a=b
      · subst b
        simp [Matrix.submatrix_apply,regularPoleDiagonal,regularLocalPolePencil,
          Matrix.blockDiagonal_apply,Matrix.diagonal_apply,Matrix.one_apply]
        split_ifs <;> ring
      · simp [Matrix.submatrix_apply,regularPoleDiagonal,regularLocalPolePencil,
          Matrix.blockDiagonal_apply,Matrix.diagonal_apply,h]
    | inr j =>
      simp [Matrix.submatrix_apply,regularLocalPolePencil,Matrix.blockDiagonal_apply]

omit [LinearOrder (m × p)] in
theorem regular_pole_block_decomposition (lam : p → K) (hlam : Function.Injective lam)
    (A B : Matrix (m × p) (m × p) K)
    (hA : A.transpose = -A) (hB : B.transpose = -B) (hBd : ∀ i, B i i=0) :
    ∃ T : Matrix ((m × p) ⊕ (m × p)) ((m ⊕ m) × p) K,
    ∃ S : Matrix ((m ⊕ m) × p) ((m × p) ⊕ (m × p)) K,
      T*S=1 ∧ S*T=1 ∧
      (T.map C).transpose * regularPolePencil (fun i : m × p => lam i.2) A B * T.map C =
        Matrix.blockDiagonal (regularLocalPolePencil lam A B) := by
  letI : LinearOrder (m × p) :=
    LinearOrder.lift' (Fintype.equivFin (m × p)) (Fintype.equivFin (m × p)).injective
  obtain ⟨T₀,S₀,hTS,hST,hcong⟩ :=
    regular_pole_constant_separation (fun i : m × p => lam i.2) A B hA hB hBd
  let e := Equiv.sumProdDistrib m m p
  refine ⟨T₀.submatrix id e,S₀.submatrix e id,?_,?_,?_⟩
  · rw [Matrix.submatrix_mul_equiv,hTS,Matrix.submatrix_id_id]
  · change S₀.submatrix e (Equiv.refl _) * T₀.submatrix (Equiv.refl _) e = 1
    rw [Matrix.submatrix_mul_equiv,hST]
    exact Matrix.submatrix_one_equiv e
  · have he :
        ((T₀.submatrix id e).map C).transpose *
            regularPolePencil (fun i : m × p => lam i.2) A B * (T₀.submatrix id e).map C =
        ((T₀.map C).transpose * regularPolePencil (fun i : m × p => lam i.2) A B * T₀.map C).submatrix e e := by
      change (T₀.map C).transpose.submatrix e (Equiv.refl _) *
        (regularPolePencil (fun i : m × p => lam i.2) A B).submatrix (Equiv.refl _) (Equiv.refl _) *
        (T₀.map C).submatrix (Equiv.refl _) e = _
      rw [Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv]
    rw [he,hcong]
    exact separated_poles_reindex lam hlam A B

end FD56
