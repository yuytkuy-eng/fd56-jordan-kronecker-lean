/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.AlternatingPencilOperator

/-! Matrix coordinates for a nondegenerate alternating primary restriction. -/

noncomputable section
namespace FD56
open Matrix
variable {K V i : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype i] [DecidableEq i]

theorem alternating_bilinear_matrix (B : LinearMap.BilinForm K V) (b : Basis i K V)
    (hB : B.IsAlt) : ∀ v, v ⬝ᵥ (BilinForm.toMatrix b B *ᵥ v)=0 := by
  apply matrix_alternating_of_skew_diag
  · ext j k
    simpa only [Matrix.transpose_apply,Matrix.neg_apply,BilinForm.toMatrix_apply]
      using (hB.neg_eq (b j) (b k)).symm
  · intro j
    simpa only [BilinForm.toMatrix_apply] using hB (b j)

theorem coordinate_matrix_range_finrank (f : Module.End K V) (b : Basis i K V) :
    Module.finrank K (LinearMap.range (Matrix.toLin' (LinearMap.toMatrix b b f)))=
      Module.finrank K (LinearMap.range f) := by
  have he : Matrix.toLin' (LinearMap.toMatrix b b f)=
      b.equivFun.toLinearMap.comp (f.comp b.equivFun.symm.toLinearMap) := by
    apply LinearMap.ext
    intro x
    apply funext
    intro j
    have h : LinearMap.toMatrix b b f *ᵥ b.equivFun (b.equivFun.symm x)=
        b.equivFun (f (b.equivFun.symm x)) :=
      f.toMatrix_mulVec_repr b b (b.equivFun.symm x)
    rw [LinearEquiv.apply_symm_apply] at h
    exact congrFun h j
  rw [he,LinearMap.range_comp,
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]
  exact (b.equivFun.submoduleMap (LinearMap.range f)).finrank_eq.symm

theorem nilpotent_coordinate_matrix (f : Module.End K V) (b : Basis i K V)
    (hf : IsNilpotent f) : IsNilpotent (LinearMap.toMatrix b b f) := by
  obtain ⟨k,hk⟩ := hf
  refine ⟨k,?_⟩
  rw [LinearMap.toMatrix_pow,hk,map_zero]

theorem primary_matrix_pair_properties [FiniteDimensional K V]
    (B : LinearMap.BilinForm K V) (f : Module.End K V)
    (hB : B.Nondegenerate) (ha : B.IsAlt) (hBf : ∀ x, B x (f x)=0)
    (hf : ∀ x y, B (f x) y=B x (f y)) (a : K)
    (b : Basis i K (f.maxGenEigenspace a)) :
    let G := BilinForm.toMatrix b (B.restrict (f.maxGenEigenspace a))
    let N := LinearMap.toMatrix b b (primaryShift f a)
    G.det≠0 ∧ (∀ v, v ⬝ᵥ (G *ᵥ v)=0) ∧
      (∀ v, v ⬝ᵥ ((G*N) *ᵥ v)=0) ∧ IsNilpotent N ∧
      Module.finrank K (LinearMap.range (Matrix.toLin' N))=
        Module.finrank K (LinearMap.range (primaryShift f a)) := by
  dsimp only
  refine ⟨(LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp
    (bilinear_primary_restriction_nondegenerate B f hf hB a),
    alternating_bilinear_matrix _ b (bilinear_primary_restriction_alternating B f ha a),
    ?_,nilpotent_coordinate_matrix _ b (primaryShift_nilpotent f a),
    coordinate_matrix_range_finrank _ b⟩
  rw [← BilinForm.toMatrix_compRight]
  exact alternating_bilinear_matrix _ b (bilinear_primary_shift_alternating B f ha hBf a)

end FD56
