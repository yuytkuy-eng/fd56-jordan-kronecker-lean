/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.KernelBasis

/-! A split polynomial equation gives a polynomial retraction of every kernel basis. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K a b k : Type*} [Field K] [Fintype a] [Fintype b] [Fintype k]
  [DecidableEq a] [DecidableEq b] [DecidableEq k]

theorem polynomial_kernel_basis_left_inverse_of_right_inverse
    (A : Matrix a b K[X]) (R : Matrix b a K[X]) (hAR : A*R=1)
    (B : Basis k K[X] (LinearMap.ker (Matrix.toLin' A))) :
    ∃ L : Matrix k b K[X], L*polynomialKernelBasisMatrix A B=1 := by
  let π : (b → K[X]) →ₗ[K[X]] LinearMap.ker (Matrix.toLin' A) :=
    { toFun := fun v => ⟨v-R *ᵥ (A *ᵥ v),by
        change A *ᵥ (v-R *ᵥ (A *ᵥ v))=0
        rw [Matrix.mulVec_sub,Matrix.mulVec_mulVec,hAR,Matrix.one_mulVec,sub_self]⟩
      map_add' := by
        intro u v
        apply Subtype.ext
        change u+v-R *ᵥ (A *ᵥ (u+v))=(u-R *ᵥ (A *ᵥ u))+(v-R *ᵥ (A *ᵥ v))
        simp only [Matrix.mulVec_add,add_sub_add_comm]
      map_smul' := by
        intro c v
        apply Subtype.ext
        change c•v-R *ᵥ (A *ᵥ (c•v))=c•(v-R *ᵥ (A *ᵥ v))
        simp only [Matrix.mulVec_smul,smul_sub,RingHom.id_apply] }
  have hπ (v : LinearMap.ker (Matrix.toLin' A)) : π v.val=v := by
    apply Subtype.ext
    change v.val-R *ᵥ (A *ᵥ v.val)=v.val
    have hv : A *ᵥ v.val=0 := v.property
    rw [hv,Matrix.mulVec_zero,sub_zero]
  let L := LinearMap.toMatrix' (B.equivFun.toLinearMap.comp π)
  refine ⟨L,?_⟩
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul,Matrix.toLin'_one]
  change (Matrix.toLin' (LinearMap.toMatrix' (B.equivFun.toLinearMap.comp π))).comp
    (Matrix.toLin' (polynomialKernelBasisMatrix A B))=LinearMap.id
  rw [Matrix.toLin'_toMatrix']
  apply LinearMap.ext
  intro v
  funext i
  change B.equivFun (π (polynomialKernelBasisMatrix A B *ᵥ v)) i=v i
  rw [polynomialKernelBasisMatrix_mulVec,hπ,B.equivFun.apply_symm_apply]

end FD56
