/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.HilbertObstruction

/-! Simultaneous permutation of the matrix indices preserves the full
polynomial SL radical and every bounded SL Hilbert function. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

theorem matrix_trace_submatrix_equiv {R a b : Type*} [AddCommMonoid R]
    [Fintype a] [Fintype b] (A : Matrix a a R) (e : b ≃ a) :
    Matrix.trace (A.submatrix e e) = Matrix.trace A := by
  exact e.sum_comp (fun i => A i i)

variable {K n m n₂ m₂ : Type*} [Field K]
  [Fintype n] [Fintype m] [Fintype n₂] [Fintype m₂]

theorem kirillov_reindex
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (X : Matrix n n K[X]) (U : Matrix n m K[X])
    (Y : Matrix n n K[X]) (W : Matrix n m K[X])
    (em : m₂ ≃ m) (en : n₂ ≃ n) :
    kirillov (M.submatrix en en) (P.submatrix em en)
      (X.submatrix en en) (U.submatrix en em)
      (Y.submatrix en en) (W.submatrix en em) = kirillov M P X U Y W := by
  simp only [kirillov, Matrix.mul_sub, Matrix.trace_sub, Matrix.submatrix_mul_equiv,
    matrix_trace_submatrix_equiv]

theorem slRadical_submatrix_equiv
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (X : Matrix n n K[X]) (U : Matrix n m K[X])
    (em : m₂ ≃ m) (en : n₂ ≃ n) (h : SLRadical M P X U) :
    SLRadical (M.submatrix en en) (P.submatrix em en)
      (X.submatrix en en) (U.submatrix en em) := by
  refine ⟨by rw [matrix_trace_submatrix_equiv]; exact h.1, ?_⟩
  intro Y W hY
  have hy : Matrix.trace (Y.submatrix en.symm en.symm) = 0 := by
    rw [matrix_trace_submatrix_equiv]
    exact hY
  have hh := h.2 (Y.submatrix en.symm en.symm) (W.submatrix en.symm em.symm) hy
  rw [← kirillov_reindex M P X U _ _ em en] at hh
  simpa [Matrix.submatrix_submatrix, Function.comp_def] using hh

theorem slRadical_reindex
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (X : Matrix n n K[X]) (U : Matrix n m K[X])
    (em : m₂ ≃ m) (en : n₂ ≃ n) :
    SLRadical (M.submatrix en en) (P.submatrix em en)
      (X.submatrix en en) (U.submatrix en em) ↔ SLRadical M P X U := by
  constructor
  · intro h
    have hh := slRadical_submatrix_equiv _ _ _ _ em.symm en.symm h
    simpa [Matrix.submatrix_submatrix, Function.comp_def] using hh
  · exact slRadical_submatrix_equiv M P X U em en

def boundedSLKernelReindexEquiv
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (em : m₂ ≃ m) (en : n₂ ≃ n) (d : ℕ) :
    boundedSLKernel (M.submatrix en en) (P.submatrix em en) d ≃ₗ[K]
      boundedSLKernel M P d where
  toFun z := ⟨(z.val.1.submatrix en.symm en.symm, z.val.2.submatrix en.symm em.symm), by
    have h := slRadical_submatrix_equiv _ _ (entries z.val.1) (entries z.val.2)
      em.symm en.symm z.property
    change SLRadical M P ((entries z.val.1).submatrix en.symm en.symm)
      ((entries z.val.2).submatrix en.symm em.symm)
    simpa [Matrix.submatrix_submatrix, Function.comp_def] using h⟩
  invFun z := ⟨(z.val.1.submatrix en en, z.val.2.submatrix en em),
    slRadical_submatrix_equiv M P (entries z.val.1) (entries z.val.2) em en z.property⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext <;> funext i j <;> simp [Matrix.submatrix_apply]
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext <;> funext i j <;> simp [Matrix.submatrix_apply]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem slHilbert_reindex
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (em : m₂ ≃ m) (en : n₂ ≃ n) (d : ℕ) :
    slHilbert (M.submatrix en en) (P.submatrix em en) d = slHilbert M P d :=
  (boundedSLKernelReindexEquiv M P em en d).finrank_eq

theorem boundedSLKernel_reindex_finrank
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (em : m₂ ≃ m) (en : n₂ ≃ n) (d : ℕ) :
    Module.finrank K (boundedSLKernel (M.submatrix en en) (P.submatrix em en) d) =
      Module.finrank K (boundedSLKernel M P d) :=
  slHilbert_reindex M P em en d

end FD56
