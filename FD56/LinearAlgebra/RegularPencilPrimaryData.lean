/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PrimarySpaceRestriction
import FD56.LinearAlgebra.AffineRatioSeparable

/-! Local pencil invariants determine the dimension and rank of the nilpotent primary restriction. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

theorem matrix_toLin_charpoly (A : Matrix n n K) : (Matrix.toLin' A).charpoly=A.charpoly := by
  rw [← LinearMap.charpoly_toMatrix _ (Pi.basisFun K n),
    LinearMap.toMatrix_eq_toMatrix',LinearMap.toMatrix'_toLin']

theorem affine_ratio_rootMultiplicity (A B : Matrix n n K) (hB : B.det≠0) (x : K) :
    rootMultiplicity x (-B⁻¹*A).charpoly=rootMultiplicity x (affineMatrixPencil A B).det := by
  have he := affine_ratio_charpoly A B B⁻¹ (Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hB))
  have hn : C B⁻¹.det*(affineMatrixPencil A B).det≠0 := by
    rw [← he]
    exact (-B⁻¹*A).charpoly_monic.ne_zero
  rw [he,rootMultiplicity_mul hn,rootMultiplicity_C,zero_add]

theorem affine_ratio_shift_kernel (A B : Matrix n n K) (hB : B.det≠0) (x : K) :
    LinearMap.ker (Matrix.toLin' (-B⁻¹*A)-x•1)=
      LinearMap.ker (Matrix.toLin' (A+x•B)) := by
  have hVB : B⁻¹*B=1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hB)
  have he : -B⁻¹*A-x•1=(-B⁻¹)*(A+x•B) := by
    simp only [Matrix.mul_add,Matrix.mul_smul,Matrix.neg_mul,hVB,smul_neg,sub_eq_add_neg]
  have hi : Function.Injective (-B⁻¹).mulVec := by
    apply Matrix.mulVec_injective_iff_isUnit.mpr
    apply IsUnit.neg
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    exact Matrix.isUnit_nonsing_inv_det B (isUnit_iff_ne_zero.mpr hB)
  have he' : Matrix.toLin' (-B⁻¹*A)-x•1=Matrix.toLin' ((-B⁻¹)*(A+x•B)) := by
    rw [← he,map_sub,map_smul,Matrix.toLin'_one]
    rfl
  rw [he']
  ext v
  change ((-B⁻¹)*(A+x•B))*ᵥv=0 ↔ (A+x•B)*ᵥv=0
  rw [← Matrix.mulVec_mulVec]
  constructor
  · intro h
    exact hi (h.trans (Matrix.mulVec_zero _).symm)
  · intro h
    rw [h,Matrix.mulVec_zero]

theorem affine_pencil_primary_rank_two (A B : Matrix n n K) (hB : B.det≠0)
    (x : K) (m : ℕ) (hm : 1≤m)
    (hmult : rootMultiplicity x (affineMatrixPencil A B).det=2*m)
    (hker : Module.finrank K (LinearMap.ker (Matrix.toLin' (A+x•B)))=2*m-2) :
    let f : Module.End K (n → K) := Matrix.toLin' (-B⁻¹*A)
    Module.finrank K (f.maxGenEigenspace x)=2*m ∧
      IsNilpotent (primaryShift f x) ∧
      Module.finrank K (LinearMap.range (primaryShift f x))=2 := by
  intro f
  have hc : rootMultiplicity x f.charpoly=2*m := by
    rw [matrix_toLin_charpoly,affine_ratio_rootMultiplicity A B hB]
    exact hmult
  refine ⟨?_,primaryShift_nilpotent f x,?_⟩
  · rw [primary_space_finrank_eq_rootMultiplicity,hc]
  · apply primaryShift_range_finrank_two f x m hm hc
    rw [affine_ratio_shift_kernel A B hB x]
    exact hker

end FD56
