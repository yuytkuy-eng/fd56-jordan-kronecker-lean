/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.RowNormalization

/-! Complete a split column family with a basis of a prescribed left kernel. -/

noncomputable section
namespace FD56
open Matrix

theorem matrix_left_inverse_column_completion {K n a : Type*} [Field K]
    [Fintype n] [Fintype a] [DecidableEq n] [DecidableEq a]
    (Q : Matrix n a K) (L : Matrix a n K) (hLQ : L*Q=1) :
    ∃ S : Matrix n (a ⊕ Fin (Fintype.card n-Fintype.card a)) K,
    ∃ T : Matrix (a ⊕ Fin (Fintype.card n-Fintype.card a)) n K,
      S*T=1 ∧ T*S=1 ∧ S.submatrix id Sum.inl=Q ∧ L*S.submatrix id Sum.inr=0 := by
  classical
  let f := Matrix.toLin' Q
  let g := Matrix.toLin' L
  have hgf (v : a → K) : g (f v)=v := by
    change L *ᵥ (Q *ᵥ v)=v
    rw [Matrix.mulVec_mulVec,hLQ,Matrix.one_mulVec]
  have hsurj : Function.Surjective g := fun v => ⟨f v,hgf v⟩
  have hk : Module.finrank K (LinearMap.ker g)=Fintype.card n-Fintype.card a := by
    have h := g.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hsurj] at h
    simp only [finrank_top,Module.finrank_fintype_fun_eq_card] at h
    omega
  let b := Module.finBasisOfFinrankEq K (LinearMap.ker g) hk
  let e := (LinearEquiv.sumArrowLequivProdArrow a (Fin (Fintype.card n-Fintype.card a)) K K).trans
    (((LinearEquiv.refl K (a → K)).prodCongr b.equivFun.symm).trans
      (splitKernelEquiv g f hgf))
  let S := LinearMap.toMatrix' e.toLinearMap
  let T := LinearMap.toMatrix' e.symm.toLinearMap
  refine ⟨S,T,?_,?_,?_,?_⟩
  · have h : e.toLinearMap.comp e.symm.toLinearMap=LinearMap.id := by ext v; simp
    simpa only [S,T,LinearMap.toMatrix'_comp,LinearMap.toMatrix'_id] using
      congrArg LinearMap.toMatrix' h
  · have h : e.symm.toLinearMap.comp e.toLinearMap=LinearMap.id := by ext v; simp
    simpa only [S,T,LinearMap.toMatrix'_comp,LinearMap.toMatrix'_id] using
      congrArg LinearMap.toMatrix' h
  · funext i j
    change (e (Pi.single (Sum.inl j) 1)) i=Q i j
    have hleft : (fun k : a => (Pi.single (Sum.inl j) (1:K) :
        (a ⊕ Fin (Fintype.card n-Fintype.card a)) → K) (Sum.inl k))=Pi.single j 1 := by
      funext k
      simp [Pi.single_apply]
    have hright : (fun k : Fin (Fintype.card n-Fintype.card a) =>
        (Pi.single (Sum.inl j) (1:K) : (a ⊕ Fin (Fintype.card n-Fintype.card a)) → K) (Sum.inr k))=0 := by
      funext k
      simp
    change (f (fun k => (Pi.single (Sum.inl j) (1:K) :
      (a ⊕ Fin (Fintype.card n-Fintype.card a)) → K) (Sum.inl k)) +
      (b.equivFun.symm (fun k => (Pi.single (Sum.inl j) (1:K) :
      (a ⊕ Fin (Fintype.card n-Fintype.card a)) → K) (Sum.inr k))).val) i=_
    rw [hleft,hright,map_zero,Submodule.coe_zero,add_zero]
    simp [f,Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Pi.single_apply]
  · funext i j
    have hleft : (fun k : a => (Pi.single (Sum.inr j) (1:K) :
        (a ⊕ Fin (Fintype.card n-Fintype.card a)) → K) (Sum.inl k))=0 := by
      funext k
      simp
    have hright : (fun k : Fin (Fintype.card n-Fintype.card a) =>
        (Pi.single (Sum.inr j) (1:K) : (a ⊕ Fin (Fintype.card n-Fintype.card a)) → K) (Sum.inr k))=Pi.single j 1 := by
      funext k
      simp [Pi.single_apply]
    have hcol : (fun k => S k (Sum.inr j)) =
        (b.equivFun.symm (Pi.single j 1)).val := by
      change e (Pi.single (Sum.inr j) 1)=_
      change f (fun k => (Pi.single (Sum.inr j) (1:K) :
        (a ⊕ Fin (Fintype.card n-Fintype.card a)) → K) (Sum.inl k)) +
        (b.equivFun.symm (fun k => (Pi.single (Sum.inr j) (1:K) :
        (a ⊕ Fin (Fintype.card n-Fintype.card a)) → K) (Sum.inr k))).val=_
      rw [hleft,hright,map_zero,zero_add]
    change (g (fun k => S k (Sum.inr j))) i=0
    rw [hcol]
    exact congrFun (b.equivFun.symm (Pi.single j 1)).property i

end FD56
