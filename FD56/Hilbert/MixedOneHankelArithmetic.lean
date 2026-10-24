/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MixedOneHankelWitness
import FD56.Hilbert.BalancedDegrees

/-! Counting the kernel and scalar terms of the quotient-one witness. -/

noncomputable section
namespace FD56
open scoped BigOperators

theorem exists_positive_balanced_hankel_degrees (u v : ℕ) (hv : 0<v) :
    ∃ h : Fin v → ℕ, (∀ j, 0<h j) ∧ (∑ j, h j)=3*u+4*v ∧
      (List.ofFn h).Perm (balancedDegreeList (3*u+4*v) v) := by
  let xs := balancedDegreeList (3*u+4*v) v
  obtain ⟨k,h,he⟩ : ∃ (k : ℕ) (h : Fin k → ℕ), List.ofFn h=xs :=
    ⟨xs.length,xs.get,List.ofFn_get xs⟩
  have hk : k=v := by simpa only [xs,List.length_ofFn,balancedDegreeList_length _ _ hv] using congrArg List.length he
  subst k
  have hs : (∑ j, h j)=3*u+4*v := by
    have hz := congrArg List.sum he
    simpa only [xs,List.sum_ofFn,balancedDegreeList_sum _ _ hv] using hz
  refine ⟨h,?_,hs,he ▸ List.Perm.refl _⟩
  intro j
  have hj : h j∈balancedDegreeList (3*u+4*v) v := by
    change h j∈xs
    rw [← he]
    exact List.mem_ofFn.mpr ⟨j,rfl⟩
  have hdiv : 0<(3*u+4*v)/v := Nat.div_pos (by omega) hv
  simp only [balancedDegreeList,List.mem_append,List.mem_replicate] at hj
  rcases hj with ⟨_,he⟩ | ⟨_,he⟩ <;> omega

theorem mixedOneHankel_heights_sum (u v d : ℕ) (h : Fin v → ℕ) :
    (∑ l, hankelScalarHeights h (mixedOneHankelDegree u v) (mixedOneHankelPairEquiv u v) d l) =
      ∑ i : Fin u ⊕ Fin v, ∑ j, (h j+(mixedKernelDegree 1 u v i+2)-(d+2)) := by
  rw [← Equiv.sum_comp (mixedOneHankelPairEquiv u v).symm]
  simp only [hankelScalarHeights,Equiv.apply_symm_apply,Fintype.sum_prod_type]
  rw [Finset.sum_comm,← Equiv.sum_comp (finSumFinEquiv : Fin u ⊕ Fin v ≃ Fin (u+v))]
  simp only [mixedOneHankelDegree,Equiv.symm_apply_apply]

set_option maxHeartbeats 800000 in
theorem mixedOneHankel_count_identity (u v d : ℕ) (h : Fin v → ℕ)
    (hd : 3≤d) (hs : ∑ j, h j=3*u+4*v) :
    (∑ i : Fin u ⊕ Fin v, ∑ j, (d-(mixedKernelDegree 1 u v i+1)+1-h j)) +
      mixedOneHankelScalarCount u v d h =
    max (∑ i : Fin u ⊕ Fin v, ∑ j, (d-(mixedKernelDegree 1 u v i+1)+1-h j))
      (((u+v)*v+1)*d+2-(3*u^2+8*u*v+6*v^2)) := by
  let G := ∑ i : Fin u ⊕ Fin v, ∑ j, (d-(mixedKernelDegree 1 u v i+1)+1-h j)
  let S := ∑ i : Fin u ⊕ Fin v, ∑ j, (h j+(mixedKernelDegree 1 u v i+2)-(d+2))
  have ht (i : Fin u ⊕ Fin v) (j : Fin v) :
      (d-(mixedKernelDegree 1 u v i+1)+1-h j)+(h j+(mixedKernelDegree 1 u v i+2)) =
      (h j+(mixedKernelDegree 1 u v i+2)-(d+2))+(d+2) := by
    cases i <;> simp only [mixedKernelDegree_inl,mixedKernelDegree_inr] <;> omega
  have he := Finset.sum_congr (show (Finset.univ : Finset (Fin u ⊕ Fin v))=Finset.univ from rfl)
    (fun i _ => Finset.sum_congr (show (Finset.univ : Finset (Fin v))=Finset.univ from rfl) (fun j _ => ht i j))
  have htots : (∑ i : Fin u ⊕ Fin v, ∑ j, (h j+(mixedKernelDegree 1 u v i+2)))=
      (u+2*v)*(3*u+4*v) := by
    simp only [Finset.sum_add_distrib,hs,Fintype.sum_sum_type,mixedKernelDegree_inl,mixedKernelDegree_inr,
      Finset.sum_const,Finset.card_univ,Fintype.card_sum,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
    ring
  have hc : (∑ _i : Fin u ⊕ Fin v, ∑ _j : Fin v, (d+2))=(u+v)*v*(d+2) := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_sum,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
    ring
  simp only [Finset.sum_add_distrib] at he htots hc
  have he' : G+(3*u^2+8*u*v+6*v^2)=S+(u+v)*v*d := by
    dsimp only [G,S]
    nlinarith only [he,htots,hc]
  have hm : ((u+v)*v+1)*d+2=(u+v)*v*d+(d+2) := by ring
  change G+mixedOneHankelScalarCount u v d h=max G _
  rw [mixedOneHankelScalarCount,mixedOneHankel_heights_sum,hm]
  change G+(d+2-S)=max G ((u+v)*v*d+(d+2)-(3*u^2+8*u*v+6*v^2))
  omega

end FD56
