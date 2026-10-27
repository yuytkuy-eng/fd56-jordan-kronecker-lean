/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.SymplecticMatrixNormalization
import FD56.Hilbert.RegularJordanBlock

/-! A scalar pencil on a symplectic space is a direct sum of simple regular blocks. -/

noncomputable section
set_option maxHeartbeats 2000000
namespace FD56
open Matrix Polynomial

def symplecticJordanIndex (n : Type*) : ((Fin 1 ⊕ Fin 1) × n) ≃ (Fin 2 × n) :=
  Equiv.prodCongr finSumFinEquiv (Equiv.refl n)

theorem standardSymplecticMatrix_simple_jordan {K : Type*} [Field K] (k : ℕ) (a : K) :
    ((X-C a) • (standardSymplecticMatrix K k).map C).submatrix
      (symplecticJordanIndex (Fin k)) (symplecticJordanIndex (Fin k)) =
      Matrix.blockDiagonal (fun _ : Fin k => skewJordanBlockPencil a 1) := by
  ext ⟨i,j⟩ ⟨u,v⟩
  by_cases h : j=v
  · subst v
    rcases i with i|i <;> rcases u with u|u <;>
      fin_cases i <;> fin_cases u <;>
      simp [standardSymplecticMatrix,symplecticJordanIndex,Matrix.blockDiagonal_apply,
        skewJordanBlockPencil,jordanUpperPencil,Matrix.smul_apply,smul_eq_mul,
        finSumFinEquiv]
  · simp [standardSymplecticMatrix,symplecticJordanIndex,Matrix.blockDiagonal_apply,
      h,Matrix.smul_apply,smul_eq_mul]

theorem scalar_alternating_pencil_simple_jordan_decomposition {K n : Type*} [Field K]
    [Fintype n] [DecidableEq n] (B : Matrix n n K)
    (hB : ∀ v : n → K, v ⬝ᵥ (B *ᵥ v)=0) (hdet : B.det≠0) (a : K) :
    ∃ k : ℕ, Fintype.card n=2*k ∧
    ∃ T : Matrix n ((Fin 1 ⊕ Fin 1) × Fin k) K,
    ∃ U : Matrix ((Fin 1 ⊕ Fin 1) × Fin k) n K,
      T*U=1 ∧ U*T=1 ∧
      (T.map C).transpose*((X-C a) • B.map C)*T.map C=
        Matrix.blockDiagonal (fun _ : Fin k => skewJordanBlockPencil a 1) := by
  obtain ⟨k,hk,T,U,hTU,hUT,he⟩ := alternating_nondegenerate_symplectic_normalization B hB hdet
  let e := symplecticJordanIndex (Fin k)
  refine ⟨k,hk,T.submatrix id e,U.submatrix e id,?_,?_,?_⟩
  · rw [Matrix.submatrix_mul_equiv,hTU,Matrix.submatrix_id_id]
  · change U.submatrix e (Equiv.refl _) * T.submatrix (Equiv.refl _) e=1
    rw [Matrix.submatrix_mul_equiv,hUT]
    exact Matrix.submatrix_one_equiv e
  · have hemap : (T.map C).transpose*B.map C*T.map C=(standardSymplecticMatrix K k).map C := by
      change T.transpose.map C*B.map C*T.map C=_
      rw [← Matrix.map_mul,← Matrix.map_mul,he]
    have hp : (T.map C).transpose*((X-C a) • B.map C)*T.map C=
        (X-C a) • (standardSymplecticMatrix K k).map C := by
      rw [Matrix.mul_smul,Matrix.smul_mul,hemap]
    simp only [← Matrix.submatrix_map]
    change (T.map C).transpose.submatrix e (Equiv.refl _) *
      ((X-C a) • B.map C).submatrix (Equiv.refl _) (Equiv.refl _) *
      (T.map C).submatrix (Equiv.refl _) e=_
    rw [Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv,hp]
    exact standardSymplecticMatrix_simple_jordan k a

end FD56
