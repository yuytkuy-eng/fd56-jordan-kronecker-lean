/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PolynomialBezout
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-! A surjective rectangular matrix admits coordinates in which it is [I 0]. -/

noncomputable section
namespace FD56
open Matrix

def splitKernelEquiv {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (f : V →ₗ[K] W) (g : W →ₗ[K] V)
    (hg : ∀ w, f (g w) = w) : (W × LinearMap.ker f) ≃ₗ[K] V where
  toFun z := g z.1 + z.2.val
  invFun v := (f v, ⟨v - g (f v), by simp [LinearMap.mem_ker, hg]⟩)
  left_inv z := by
    have hz : f z.2.val = 0 := z.2.property
    apply Prod.ext
    · simp [map_add, hg, hz]
    · apply Subtype.ext
      simp only [map_add, hg, hz, add_zero]
      abel
  right_inv v := by dsimp; abel
  map_add' z w := by simp only [Prod.fst_add, Prod.snd_add, map_add, Submodule.coe_add]; abel
  map_smul' c z := by simp [smul_add]

theorem splitKernelEquiv_projection {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] W) (g : W →ₗ[K] V) (hg : ∀ w, f (g w) = w)
    (z : W × LinearMap.ker f) : f (splitKernelEquiv f g hg z) = z.1 := by
  have hz : f z.2.val = 0 := z.2.property
  change f (g z.1 + z.2.val) = z.1
  rw [map_add, hg, hz, add_zero]

theorem surjective_matrix_kernel_finrank {K n m : Type*} [Field K]
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (P : Matrix m n K) (hP : Function.Surjective P.mulVec) :
    Module.finrank K (LinearMap.ker (Matrix.toLin' P)) = Fintype.card n - Fintype.card m := by
  have h := (Matrix.toLin' P).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hP] at h
  simp only [finrank_top, Module.finrank_fintype_fun_eq_card] at h
  omega

theorem surjective_matrix_normalization {K n m : Type*} [Field K]
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (P : Matrix m n K) (hP : Function.Surjective P.mulVec) :
    ∃ (S : Matrix n (m ⊕ Fin (Fintype.card n - Fintype.card m)) K)
      (I : Matrix (m ⊕ Fin (Fintype.card n - Fintype.card m)) n K),
      S * I = 1 ∧ I * S = 1 ∧ P * S = Matrix.fromCols 1 0 := by
  let f := Matrix.toLin' P
  obtain ⟨g, hg⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hP)
  have hg' : ∀ w, f (g w) = w := fun w => congrArg (fun t : (m → K) →ₗ[K] (m → K) => t w) hg
  let b := Module.finBasisOfFinrankEq K (LinearMap.ker f) (surjective_matrix_kernel_finrank P hP)
  let e := (LinearEquiv.sumArrowLequivProdArrow m (Fin (Fintype.card n - Fintype.card m)) K K).trans
    (((LinearEquiv.refl K (m → K)).prodCongr b.equivFun.symm).trans (splitKernelEquiv f g hg'))
  refine ⟨LinearMap.toMatrix' e.toLinearMap, LinearMap.toMatrix' e.symm.toLinearMap, ?_, ?_, ?_⟩
  · have h : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by ext v; simp
    simpa only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id] using congrArg LinearMap.toMatrix' h
  · have h : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by ext v; simp
    simpa only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id] using congrArg LinearMap.toMatrix' h
  · have h : f.comp e.toLinearMap = Matrix.toLin' (Matrix.fromCols 1 0) := by
      apply LinearMap.ext
      intro v
      change f (splitKernelEquiv f g hg' (v ∘ Sum.inl, b.equivFun.symm (v ∘ Sum.inr))) = _
      rw [splitKernelEquiv_projection]
      ext i
      simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
        Matrix.one_apply]
    simpa only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', f] using
      congrArg LinearMap.toMatrix' h

end FD56
