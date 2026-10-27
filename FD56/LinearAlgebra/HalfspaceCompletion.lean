/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.RowNormalization

/-! Extend an injective half-dimensional column family to constant coordinates. -/

noncomputable section
namespace FD56
open Matrix

theorem injective_half_matrix_completion {K a : Type*} [Field K]
    [Fintype a] [DecidableEq a] (d : ℕ) (Q : Matrix a (Fin d) K)
    (hQ : Function.Injective Q.mulVec) (ha : Fintype.card a=2*d) :
    ∃ S : Matrix a (Fin d ⊕ Fin d) K,
    ∃ T : Matrix (Fin d ⊕ Fin d) a K,
      S*T=1 ∧ T*S=1 ∧ S.submatrix id Sum.inr=Q := by
  classical
  let f := Matrix.toLin' Q
  obtain ⟨g,hg⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hQ)
  have hg' (v : Fin d → K) : g (f v)=v :=
    congrArg (fun L : (Fin d → K) →ₗ[K] (Fin d → K) => L v) hg
  have hsurj : Function.Surjective g := fun v => ⟨f v,hg' v⟩
  have hk : Module.finrank K (LinearMap.ker g)=d := by
    have h := g.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hsurj] at h
    simp only [finrank_top,Module.finrank_fintype_fun_eq_card,Fintype.card_fin,ha] at h
    omega
  let b := Module.finBasisOfFinrankEq K (LinearMap.ker g) hk
  let e := (LinearEquiv.sumArrowLequivProdArrow (Fin d) (Fin d) K K).trans
    ((LinearEquiv.prodComm K (Fin d → K) (Fin d → K)).trans
      (((LinearEquiv.refl K (Fin d → K)).prodCongr b.equivFun.symm).trans
        (splitKernelEquiv g f hg')))
  refine ⟨LinearMap.toMatrix' e.toLinearMap,LinearMap.toMatrix' e.symm.toLinearMap,?_,?_,?_⟩
  · have h : e.toLinearMap.comp e.symm.toLinearMap=LinearMap.id := by ext v; simp
    simpa only [LinearMap.toMatrix'_comp,LinearMap.toMatrix'_id] using
      congrArg LinearMap.toMatrix' h
  · have h : e.symm.toLinearMap.comp e.toLinearMap=LinearMap.id := by ext v; simp
    simpa only [LinearMap.toMatrix'_comp,LinearMap.toMatrix'_id] using
      congrArg LinearMap.toMatrix' h
  · funext i j
    change (e (Pi.single (Sum.inr j) 1)) i=Q i j
    have hleft : (fun k : Fin d => (Pi.single (Sum.inr j) (1:K) : (Fin d ⊕ Fin d) → K) (Sum.inl k))=0 := by
      funext k
      simp
    have hright : (fun k : Fin d => (Pi.single (Sum.inr j) (1:K) : (Fin d ⊕ Fin d) → K) (Sum.inr k))=Pi.single j 1 := by
      funext k
      simp [Pi.single_apply]
    change (f (fun k => (Pi.single (Sum.inr j) (1:K) : (Fin d ⊕ Fin d) → K) (Sum.inr k)) +
      (b.equivFun.symm (fun k => (Pi.single (Sum.inr j) (1:K) : (Fin d ⊕ Fin d) → K) (Sum.inl k))).val) i=_
    rw [hleft,hright,map_zero,Submodule.coe_zero,add_zero]
    simp [f,Matrix.toLin'_apply,Matrix.mulVec, dotProduct,Pi.single_apply]

end FD56
