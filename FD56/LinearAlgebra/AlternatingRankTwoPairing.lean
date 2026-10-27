/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.AlternatingRankTwo

/-! Two nonorthogonal vectors detect the radical of a rank-two alternating form. -/

noncomputable section
namespace FD56
open Matrix

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

theorem alternating_rank_two_pairing_coordinates (A : Matrix n n K)
    (hA : ∀ w : n → K, w ⬝ᵥ (A *ᵥ w)=0)
    (hr : Module.finrank K (LinearMap.range (Matrix.toLin' A))≤2)
    (u v : n → K) (hc : u ⬝ᵥ (A *ᵥ v)≠0) :
    Function.Injective (fun z : LinearMap.range (Matrix.toLin' A) =>
      (u ⬝ᵥ z.val,v ⬝ᵥ z.val)) := by
  let f : LinearMap.range (Matrix.toLin' A) →ₗ[K] K × K :=
    { toFun := fun z => (u ⬝ᵥ z.val,v ⬝ᵥ z.val)
      map_add' := by intros; simp only [Submodule.coe_add,dotProduct_add]; rfl
      map_smul' := by intros; simp only [Submodule.coe_smul,dotProduct_smul]; rfl }
  let c := u ⬝ᵥ (A *ᵥ v)
  have hc' : c≠0 := hc
  have hpair : v ⬝ᵥ (A *ᵥ u) = -c := by
    have hh := hA (u+v)
    simp only [Matrix.mulVec_add,add_dotProduct,dotProduct_add,hA,zero_add,add_zero] at hh
    exact eq_neg_of_add_eq_zero_left hh
  have hs : Function.Surjective f := by
    rintro ⟨x,y⟩
    let w := (-y/c) • u + (x/c) • v
    refine ⟨⟨A *ᵥ w,⟨w,rfl⟩⟩,?_⟩
    change (u ⬝ᵥ (A *ᵥ w),v ⬝ᵥ (A *ᵥ w))=(x,y)
    apply Prod.ext <;>
      simp only [w,Matrix.mulVec_add,Matrix.mulVec_smul,dotProduct_add,dotProduct_smul,
        hA,hpair,smul_eq_mul,mul_zero,zero_add,add_zero]
    · change (x/c)*c=x
      field_simp
    · field_simp
  have hh := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs,finrank_top,Module.finrank_prod,Module.finrank_self] at hh
  have hk : Module.finrank K (LinearMap.ker f)=0 := by omega
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hk)

theorem alternating_rank_two_radical_of_two_pairings (A : Matrix n n K)
    (hA : ∀ w : n → K, w ⬝ᵥ (A *ᵥ w)=0)
    (hr : Module.finrank K (LinearMap.range (Matrix.toLin' A))≤2)
    (u v w : n → K) (hc : u ⬝ᵥ (A *ᵥ v)≠0)
    (hu : u ⬝ᵥ (A *ᵥ w)=0) (hv : v ⬝ᵥ (A *ᵥ w)=0) : A *ᵥ w=0 := by
  let z : LinearMap.range (Matrix.toLin' A) := ⟨A *ᵥ w,⟨w,rfl⟩⟩
  have he : (u ⬝ᵥ z.val,v ⬝ᵥ z.val)=
      (u ⬝ᵥ (0 : LinearMap.range (Matrix.toLin' A)).val,
       v ⬝ᵥ (0 : LinearMap.range (Matrix.toLin' A)).val) := by
    simp only [z,hu,hv,ZeroMemClass.coe_zero,dotProduct_zero]
  exact congrArg Subtype.val (alternating_rank_two_pairing_coordinates A hA hr u v hc he)

theorem alternating_rank_two_radical_of_image_pairings (A B N : Matrix n n K)
    (hNA : N.transpose*B=A)
    (hA : ∀ w : n → K, w ⬝ᵥ (A *ᵥ w)=0)
    (hr : Module.finrank K (LinearMap.range (Matrix.toLin' A))≤2)
    (u v w : n → K) (hc : u ⬝ᵥ (A *ᵥ v)≠0)
    (hu : (N *ᵥ u) ⬝ᵥ (B *ᵥ w)=0) (hv : (N *ᵥ v) ⬝ᵥ (B *ᵥ w)=0) :
    A *ᵥ w=0 := by
  apply alternating_rank_two_radical_of_two_pairings A hA hr u v w hc
  · rw [← hNA,← Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,Matrix.vecMul_transpose]
    exact hu
  · rw [← hNA,← Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,Matrix.vecMul_transpose]
    exact hv

theorem alternating_rank_two_orthogonal_columns {a r : Type*}
    [Fintype a] [Fintype r] [DecidableEq a] [DecidableEq r]
    (A B N : Matrix n n K) (Q : Matrix n a K) (R : Matrix n r K)
    (hNA : N.transpose*B=A)
    (hA : ∀ w : n → K, w ⬝ᵥ (A *ᵥ w)=0)
    (hr : Module.finrank K (LinearMap.range (Matrix.toLin' A))≤2)
    (u v : n → K) (hc : u ⬝ᵥ (A *ᵥ v)≠0)
    (i j : a) (hu : (fun k => Q k i)=N *ᵥ u) (hv : (fun k => Q k j)=N *ᵥ v)
    (hQR : Q.transpose*B*R=0) : A*R=0 := by
  ext k l
  have horth (p : a) : (fun k => Q k p) ⬝ᵥ (B *ᵥ (fun k => R k l))=0 := by
    have hh := congrArg (fun M => M p l) hQR
    change ((Q.transpose*B) *ᵥ (fun k => R k l)) p=0 at hh
    rw [← Matrix.mulVec_mulVec] at hh
    exact hh
  have hzero := alternating_rank_two_radical_of_image_pairings A B N hNA hA hr
    u v (fun k => R k l) hc (hu ▸ horth i) (hv ▸ horth j)
  exact congrFun hzero k

end FD56
