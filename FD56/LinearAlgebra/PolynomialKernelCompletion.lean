/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PolynomialKernelSplitting
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.Degree.Units

/-! A right inverse and an actual kernel basis give mutually inverse polynomial
completion matrices. Square completions have nonzero constant determinant. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K a b k : Type*} [Field K] [Fintype a] [Fintype b] [Fintype k]
  [DecidableEq a] [DecidableEq b] [DecidableEq k]

theorem polynomial_kernel_basis_completion
    (A : Matrix a b K[X]) (R : Matrix b a K[X]) (hAR : A*R=1)
    (B : Basis k K[X] (LinearMap.ker (Matrix.toLin' A))) :
    ∃ L : Matrix k b K[X],
      L*polynomialKernelBasisMatrix A B=1 ∧ L*R=0 ∧
      polynomialKernelBasisMatrix A B*L+R*A=1 ∧
      Matrix.fromRows A L*Matrix.fromCols R (polynomialKernelBasisMatrix A B)=1 ∧
      Matrix.fromCols R (polynomialKernelBasisMatrix A B)*Matrix.fromRows A L=1 := by
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
  let V := polynomialKernelBasisMatrix A B
  let L := LinearMap.toMatrix' (B.equivFun.toLinearMap.comp π)
  have hLv (v : b → K[X]) : L *ᵥ v=B.equivFun (π v) := by
    change Matrix.toLin' (LinearMap.toMatrix' (B.equivFun.toLinearMap.comp π)) v=_
    rw [Matrix.toLin'_toMatrix']
    rfl
  have hLV : L*V=1 := by
    apply Matrix.ext_of_mulVec_single
    intro j
    rw [← Matrix.mulVec_mulVec,hLv,Matrix.one_mulVec]
    change B.equivFun (π (polynomialKernelBasisMatrix A B *ᵥ Pi.single j 1))=_
    rw [polynomialKernelBasisMatrix_mulVec,hπ,B.equivFun.apply_symm_apply]
  have hLR : L*R=0 := by
    apply Matrix.ext_of_mulVec_single
    intro j
    rw [← Matrix.mulVec_mulVec,hLv,Matrix.zero_mulVec]
    have hz : π (R *ᵥ Pi.single j 1)=0 := by
      apply Subtype.ext
      change R *ᵥ Pi.single j 1-R *ᵥ (A *ᵥ (R *ᵥ Pi.single j 1))=0
      simp only [Matrix.mulVec_mulVec,Matrix.mul_assoc,hAR,Matrix.mul_one,sub_self]
    rw [hz,map_zero]
  have hVL (v : b → K[X]) : V *ᵥ (L *ᵥ v)=v-R *ᵥ (A *ᵥ v) := by
    rw [hLv]
    change polynomialKernelBasisMatrix A B *ᵥ B.equivFun (π v)=_
    rw [polynomialKernelBasisMatrix_mulVec,B.equivFun.symm_apply_apply]
    rfl
  have hsplit : V*L+R*A=1 := by
    apply Matrix.ext_of_mulVec_single
    intro j
    rw [Matrix.add_mulVec,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,
      hVL,Matrix.one_mulVec,sub_add_cancel]
  have hAV : A*V=0 := polynomialKernelBasisMatrix_mul A B
  refine ⟨L,hLV,hLR,hsplit,?_,?_⟩
  · rw [Matrix.fromRows_mul_fromCols,hAR,hAV,hLR,hLV,Matrix.fromBlocks_one]
  · rw [Matrix.fromCols_mul_fromRows,add_comm]
    exact hsplit

theorem polynomial_kernel_completion_det_constant
    (A : Matrix a (a ⊕ k) K[X]) (R : Matrix (a ⊕ k) a K[X]) (hAR : A*R=1)
    (B : Basis k K[X] (LinearMap.ker (Matrix.toLin' A))) :
    ∃ c : K, c≠0 ∧ (Matrix.fromCols R (polynomialKernelBasisMatrix A B)).det=C c := by
  obtain ⟨L,_,_,_,_,hHJ⟩ := polynomial_kernel_basis_completion A R hAR B
  have hd : (Matrix.fromCols R (polynomialKernelBasisMatrix A B)).det *
      (Matrix.fromRows A L).det=1 := by
    rw [← Matrix.det_mul,hHJ,Matrix.det_one]
  have hu : IsUnit (Matrix.fromCols R (polynomialKernelBasisMatrix A B)).det :=
    isUnit_iff_dvd_one.mpr ⟨_,hd.symm⟩
  obtain ⟨c,hc,he⟩ := Polynomial.isUnit_iff.mp hu
  exact ⟨c,hc.ne_zero,he.symm⟩

end FD56
