/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.RegularDimension

/-! Removing redundant output rows splits off their free translation coordinates. -/

noncomputable section
namespace FD56
open Matrix

variable {K n m r : Type*} [Field K] [Fintype n] [Fintype m] [Fintype r]
  [DecidableEq n] [DecidableEq m] [DecidableEq r]

def outputRightMultiplication (V : Matrix m r K) :
    Matrix n m K →ₗ[K] Matrix n r K where
  toFun U := U*V
  map_add' U W := Matrix.add_mul U W V
  map_smul' c U := Matrix.smul_mul c U V

def glOutputFactorEquiv (M : Matrix n n K) (P : Matrix r n K)
    (V : Matrix m r K) (L : Matrix r m K) (hLV : L*V=1) :
    glStabilizerSpace M (V*P) ≃ₗ[K]
      glStabilizerSpace M P × LinearMap.ker (outputRightMultiplication (n := n) V) where
  toFun z := (⟨(z.val.1,z.val.2*V),by
    constructor
    · have h := congrArg (fun A => L*A) z.property.1
      simpa only [← Matrix.mul_assoc,hLV,Matrix.one_mul,Matrix.mul_zero] using h
    · simpa only [Matrix.mul_assoc] using z.property.2⟩,
    ⟨z.val.2-z.val.2*V*L,by
      change (z.val.2-z.val.2*V*L)*V=0
      simp only [Matrix.sub_mul,Matrix.mul_assoc,hLV,Matrix.mul_one,sub_self]⟩)
  invFun z := ⟨(z.1.val.1,z.1.val.2*L+z.2.val),by
    have hz : z.2.val*V=0 := z.2.property
    constructor
    · rw [Matrix.mul_assoc,z.1.property.1,Matrix.mul_zero]
    · rw [Matrix.add_mul,← Matrix.mul_assoc,Matrix.mul_assoc z.1.val.2,
        hLV,Matrix.mul_one,← Matrix.mul_assoc,hz,Matrix.zero_mul,add_zero]
      exact z.1.property.2⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · dsimp
      abel
  right_inv z := by
    have hz : z.2.val*V=0 := z.2.property
    have hu : (z.1.val.2*L+z.2.val)*V=z.1.val.2 := by
      rw [Matrix.add_mul,Matrix.mul_assoc,hLV,Matrix.mul_one,hz,add_zero]
    apply Prod.ext
    · apply Subtype.ext
      apply Prod.ext
      · rfl
      · exact hu
    · apply Subtype.ext
      change z.1.val.2*L+z.2.val-(z.1.val.2*L+z.2.val)*V*L=z.2.val
      rw [hu]
      abel
  map_add' z w := by
    apply Prod.ext
    · apply Subtype.ext
      apply Prod.ext
      · rfl
      · exact Matrix.add_mul _ _ _
    · apply Subtype.ext
      change (z.val.2+w.val.2)-(z.val.2+w.val.2)*V*L=
        (z.val.2-z.val.2*V*L)+(w.val.2-w.val.2*V*L)
      simp only [Matrix.add_mul]
      abel
  map_smul' c z := by
    apply Prod.ext
    · apply Subtype.ext
      apply Prod.ext
      · rfl
      · exact Matrix.smul_mul c _ _
    · apply Subtype.ext
      change c • z.val.2-(c • z.val.2)*V*L=c • (z.val.2-z.val.2*V*L)
      simp only [Matrix.smul_mul,smul_sub]

theorem gl_output_factor_finrank (M : Matrix n n K) (P : Matrix r n K)
    (V : Matrix m r K) (L : Matrix r m K) (hLV : L*V=1) :
    Module.finrank K (glStabilizerSpace M (V*P))=
      Module.finrank K (glStabilizerSpace M P)+Fintype.card n*(Fintype.card m-Fintype.card r) := by
  have hs : Function.Surjective (outputRightMultiplication (n := n) V) := by
    intro U
    refine ⟨U*L,?_⟩
    change U*L*V=U
    rw [Matrix.mul_assoc,hLV,Matrix.mul_one]
  have hd := (outputRightMultiplication (n := n) V).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs,finrank_top,
    Module.finrank_matrix,Module.finrank_matrix] at hd
  simp only [Module.finrank_self,mul_one] at hd
  rw [(glOutputFactorEquiv M P V L hLV).finrank_eq,Module.finrank_prod]
  congr 1
  rw [Nat.mul_sub_left_distrib]
  omega

theorem unobservableSpace_output_factor (M : Matrix n n K) (P : Matrix r n K)
    (V : Matrix m r K) (L : Matrix r m K) (hLV : L*V=1) (q : ℕ) :
    unobservableSpace M (V*P) q=unobservableSpace M P q := by
  ext v
  rw [mem_unobservableSpace_iff,mem_unobservableSpace_iff]
  constructor
  · intro h i hi
    have hh := congrArg (fun w => L*ᵥw) (h i hi)
    simpa only [Matrix.mulVec_mulVec,← Matrix.mul_assoc,hLV,
      Matrix.one_mul,Matrix.mulVec_zero] using hh
  · intro h i hi
    rw [← Matrix.mulVec_mulVec,h i hi,Matrix.mulVec_zero]

theorem matrix_output_factorization (P : Matrix m n K) (d : ℕ)
    (hd : Module.finrank K (LinearMap.range (Matrix.toLin' P))=d) :
    ∃ (Q : Matrix (Fin d) n K) (V : Matrix m (Fin d) K) (L : Matrix (Fin d) m K),
      V*Q=P ∧ L*V=1 ∧ Function.Surjective Q.mulVec := by
  let f := Matrix.toLin' P
  let b := Module.finBasisOfFinrankEq K (LinearMap.range f) hd
  let v := (LinearMap.range f).subtype.comp b.equivFun.symm.toLinearMap
  let p := b.equivFun.toLinearMap.comp f.rangeRestrict
  let V := LinearMap.toMatrix' v
  let Q := LinearMap.toMatrix' p
  have hV : Function.Injective V.mulVec := by
    change Function.Injective (Matrix.toLin' (LinearMap.toMatrix' v))
    rw [Matrix.toLin'_toMatrix']
    exact (LinearMap.range f).subtype_injective.comp b.equivFun.symm.injective
  obtain ⟨L,hL⟩ := matrix_left_inverse_of_injective V hV
  refine ⟨Q,V,L,?_,hL,?_⟩
  · have he : v.comp p=f := by
      ext x
      simp only [v,p,LinearMap.comp_apply,LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply]
      rfl
    simpa only [V,Q,LinearMap.toMatrix'_comp,LinearMap.toMatrix'_toLin',f] using
      congrArg LinearMap.toMatrix' he
  · change Function.Surjective (Matrix.toLin' (LinearMap.toMatrix' p))
    rw [Matrix.toLin'_toMatrix']
    exact b.equivFun.surjective.comp f.surjective_rangeRestrict

end FD56
