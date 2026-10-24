/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.KernelBasis

/-! A unique coordinate description determines a basis of a matrix kernel. -/

noncomputable section
namespace FD56
open Matrix
open scoped BigOperators

theorem kernel_basis_of_unique_coordinates {R a b k : Type*} [CommRing R]
    [Fintype b] [DecidableEq b] [Fintype k] [DecidableEq k]
    (A : Matrix a b R) (Z : Matrix b k R)
    (hex : ∀ x, A *ᵥ x=0 ↔ ∃! v : k → R, x=Z *ᵥ v) :
    ∃ B : Basis k R (LinearMap.ker (Matrix.toLin' A)), ∀ i j, (B j).val i=Z i j := by
  have hinj : Function.Injective Z.mulVec := by
    obtain ⟨v,hv,hu⟩ := (hex 0).mp (by simp)
    have hv0 : (0 : k → R)=v := hu 0 (by simp)
    intro x y hxy
    have he : (0 : b → R)=Z *ᵥ (x-y) := by rw [Matrix.mulVec_sub,hxy,sub_self]
    have hz : x-y=0 := (hu (x-y) he).trans hv0.symm
    exact sub_eq_zero.mp hz
  have hmem (v : k → R) : A *ᵥ (Z *ᵥ v)=0 := by
    apply (hex _).mpr
    exact ⟨v,rfl,fun w hw => hinj hw.symm⟩
  let f : (k → R) →ₗ[R] LinearMap.ker (Matrix.toLin' A) :=
    (Matrix.toLin' Z).codRestrict _ hmem
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      exact hinj (congrArg Subtype.val hxy)
    · intro x
      obtain ⟨v,hv,_⟩ := (hex x.val).mp x.property
      exact ⟨v,Subtype.ext hv.symm⟩
  let e := LinearEquiv.ofBijective f hf
  refine ⟨(Pi.basisFun R k).map e, ?_⟩
  intro i j
  simp [Basis.map_apply,e,f,Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Pi.basisFun_apply,Pi.single_apply]

end FD56
