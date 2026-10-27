/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.SelfAdjointFitting
import FD56.LinearAlgebra.PrimarySpaceRestriction
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-! Nondegenerate alternating forms on primary spaces of a self-adjoint operator. -/

noncomputable section
namespace FD56
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem bilinear_primary_restriction_nondegenerate
    (B : LinearMap.BilinForm K V) (f : Module.End K V)
    (hf : ∀ x y, B (f x) y=B x (f y)) (hB : B.Nondegenerate) (a : K) :
    (B.restrict (f.maxGenEigenspace a)).Nondegenerate := by
  have hU : f.maxGenEigenspace a =
      LinearMap.ker ((f-a•1)^Module.finrank K V) := by
    rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank,Module.End.genEigenspace_nat]
  obtain ⟨hc,ho⟩ := bilinear_self_adjoint_fitting_orthogonal B f hf a
  intro x hx
  apply Subtype.ext
  apply bilinear_restriction_nondegenerate_of_orthogonal_complement B _ _ hc hB ho
  · rw [← hU]
    exact x.property
  · intro y hy
    exact hx ⟨y,hU.symm ▸ hy⟩

theorem bilinear_primary_restriction_alternating
    (B : LinearMap.BilinForm K V) (f : Module.End K V) (hB : B.IsAlt) (a : K) :
    (B.restrict (f.maxGenEigenspace a)).IsAlt := fun x => hB x.val

theorem bilinear_primary_shift_alternating
    (B : LinearMap.BilinForm K V) (f : Module.End K V)
    (hB : B.IsAlt) (hBf : ∀ x, B x (f x)=0) (a : K) :
    ((B.restrict (f.maxGenEigenspace a)).compRight (primaryShift f a)).IsAlt := by
  intro x
  change B x.val ((f-algebraMap K (Module.End K V) a) x.val)=0
  simp only [LinearMap.sub_apply,Module.algebraMap_end_apply,map_sub,map_smul,
    hBf,hB x.val,smul_zero,sub_zero]

end FD56
