/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.SelfAdjointPrimaryDecomposition
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-! Constant coordinate matrices assembling local primary congruences. -/

noncomputable section
namespace FD56
open Matrix
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [IsAlgClosed K]

local instance : DecidableEq K := Classical.decEq K

theorem primaryCollectedBasis_toMatrix
    (B : LinearMap.BilinForm K V) (f : Module.End K V)
    (hf : ∀ x y, B (f x) y=B x (f y))
    {α : f.Eigenvalues → Type*} [∀ a, Fintype (α a)] [∀ a, DecidableEq (α a)]
    (e : ∀ a, Basis (α a) K (f.maxGenEigenspace a.val)) :
    BilinForm.toMatrix (primaryCollectedBasis f e) B=
      Matrix.blockDiagonal' (fun a => BilinForm.toMatrix (e a)
        (B.restrict (f.maxGenEigenspace a.val))) := by
  ext ⟨a,i⟩ ⟨b,j⟩
  by_cases h : a=b
  · subst b
    simp only [Matrix.blockDiagonal'_apply_eq,BilinForm.toMatrix_apply,
      primaryCollectedBasis_apply,LinearMap.BilinForm.restrict_apply]
    rfl
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h,BilinForm.toMatrix_apply]
    exact primaryCollectedBasis_pairing_zero B f hf e ⟨a,i⟩ ⟨b,j⟩ h

theorem primaryCollectedBasis_operator_toMatrix
    (B : LinearMap.BilinForm K V) (f : Module.End K V)
    (hf : ∀ x y, B (f x) y=B x (f y))
    {α : f.Eigenvalues → Type*} [∀ a, Fintype (α a)] [∀ a, DecidableEq (α a)]
    (e : ∀ a, Basis (α a) K (f.maxGenEigenspace a.val)) :
    BilinForm.toMatrix (primaryCollectedBasis f e) (B.compRight f)=
      Matrix.blockDiagonal' (fun a => BilinForm.toMatrix (e a)
        ((B.compRight f).restrict (f.maxGenEigenspace a.val))) := by
  ext ⟨a,i⟩ ⟨b,j⟩
  by_cases h : a=b
  · subst b
    simp only [Matrix.blockDiagonal'_apply_eq,BilinForm.toMatrix_apply,
      primaryCollectedBasis_apply,LinearMap.BilinForm.restrict_apply]
    rfl
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h,BilinForm.toMatrix_apply]
    exact primaryCollectedBasis_operator_pairing_zero B f hf e ⟨a,i⟩ ⟨b,j⟩ h

theorem primary_local_congruence_assembly
    (B : LinearMap.BilinForm K V) (f : Module.End K V)
    (hf : ∀ x y, B (f x) y=B x (f y))
    {i : Type*} [Fintype i] [DecidableEq i] (b : Basis i K V)
    {α β : f.Eigenvalues → Type*}
    [∀ a, Fintype (α a)] [∀ a, DecidableEq (α a)]
    [∀ a, Fintype (β a)] [∀ a, DecidableEq (β a)]
    (e : ∀ a, Basis (α a) K (f.maxGenEigenspace a.val))
    (T : ∀ a, Matrix (α a) (β a) K) (S : ∀ a, Matrix (β a) (α a) K)
    (G H : ∀ a, Matrix (β a) (β a) K)
    (hTS : ∀ a, T a*S a=1) (hST : ∀ a, S a*T a=1)
    (hG : ∀ a, (T a).transpose * BilinForm.toMatrix (e a)
      (B.restrict (f.maxGenEigenspace a.val)) * T a=G a)
    (hH : ∀ a, (T a).transpose * BilinForm.toMatrix (e a)
      ((B.compRight f).restrict (f.maxGenEigenspace a.val)) * T a=H a) :
    ∃ U : Matrix i (Σ a, β a) K, ∃ W : Matrix (Σ a, β a) i K,
      U*W=1 ∧ W*U=1 ∧
      U.transpose * BilinForm.toMatrix b B * U=Matrix.blockDiagonal' G ∧
      U.transpose * BilinForm.toMatrix b (B.compRight f) * U=Matrix.blockDiagonal' H := by
  let c := primaryCollectedBasis f e
  let Y := b.toMatrix c
  let Z := c.toMatrix b
  have hYZ : Y*Z=1 := Basis.toMatrix_mul_toMatrix_flip _ _
  have hZY : Z*Y=1 := Basis.toMatrix_mul_toMatrix_flip _ _
  have hdiagTS : Matrix.blockDiagonal' T * Matrix.blockDiagonal' S=1 := by
    rw [← Matrix.blockDiagonal'_mul]
    simp only [hTS]
    exact Matrix.blockDiagonal'_one
  have hdiagST : Matrix.blockDiagonal' S * Matrix.blockDiagonal' T=1 := by
    rw [← Matrix.blockDiagonal'_mul]
    simp only [hST]
    exact Matrix.blockDiagonal'_one
  refine ⟨Y * Matrix.blockDiagonal' T,Matrix.blockDiagonal' S * Z,?_,?_,?_,?_⟩
  · calc
      _ = Y*(Matrix.blockDiagonal' T*Matrix.blockDiagonal' S)*Z := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hdiagTS,Matrix.mul_one,hYZ]
  · rw [Matrix.mul_assoc,← Matrix.mul_assoc Z,hZY,Matrix.one_mul,hdiagST]
  · rw [Matrix.transpose_mul]
    calc
      _ = (Matrix.blockDiagonal' T).transpose *
          (Y.transpose * BilinForm.toMatrix b B * Y) * Matrix.blockDiagonal' T := by
        simp only [Matrix.mul_assoc]
      _ = (Matrix.blockDiagonal' T).transpose *
          BilinForm.toMatrix c B * Matrix.blockDiagonal' T := by
        rw [BilinForm.toMatrix_mul_basis_toMatrix]
      _ = _ := by
        rw [primaryCollectedBasis_toMatrix B f hf e,Matrix.blockDiagonal'_transpose,
          ← Matrix.blockDiagonal'_mul,← Matrix.blockDiagonal'_mul]
        exact congrArg (fun M : ∀ a, Matrix (β a) (β a) K =>
          Matrix.blockDiagonal' M) (funext hG)
  · rw [Matrix.transpose_mul]
    calc
      _ = (Matrix.blockDiagonal' T).transpose *
          (Y.transpose * BilinForm.toMatrix b (B.compRight f) * Y) * Matrix.blockDiagonal' T := by
        simp only [Matrix.mul_assoc]
      _ = (Matrix.blockDiagonal' T).transpose *
          BilinForm.toMatrix c (B.compRight f) * Matrix.blockDiagonal' T := by
        rw [BilinForm.toMatrix_mul_basis_toMatrix]
      _ = _ := by
        rw [primaryCollectedBasis_operator_toMatrix B f hf e,Matrix.blockDiagonal'_transpose,
          ← Matrix.blockDiagonal'_mul,← Matrix.blockDiagonal'_mul]
        exact congrArg (fun M : ∀ a, Matrix (β a) (β a) K =>
          Matrix.blockDiagonal' M) (funext hH)

end FD56
