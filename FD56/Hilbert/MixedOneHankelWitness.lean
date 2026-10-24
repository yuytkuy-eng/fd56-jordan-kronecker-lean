/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericHankelScalar
import FD56.Hilbert.MixedSLGeneralRealization
import FD56.Hilbert.GenericKernelExtension

/-! A simultaneous kernel and scalar witness for arbitrary quotient-one sizes. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

def mixedOneHankelDegree (u v : ℕ) (i : Fin (u+v)) : ℕ :=
  mixedKernelDegree 1 u v (finSumFinEquiv.symm i)+2

def mixedOneHankelRows (u v : ℕ) :
    MixedScalarRows 1 (Fin u) (Fin v) ≃ Fin (u+v) ⊕ Fin v :=
  Fintype.equivOfCardEq (by simp [MixedScalarRows]; omega)

theorem mixedOneHankelDegree_sum (u v : ℕ) :
    (∑ i, mixedOneHankelDegree u v i)=3*u+4*v := by
  rw [← Equiv.sum_comp (finSumFinEquiv : Fin u ⊕ Fin v ≃ Fin (u+v))]
  simp [mixedOneHankelDegree,Fintype.sum_sum_type]
  omega

theorem mixedOneHankelDegree_pos (u v : ℕ) (i : Fin (u+v)) :
    0<mixedOneHankelDegree u v i := by
  unfold mixedOneHankelDegree
  omega

theorem mixedOneHankelDegree_le (u v d : ℕ) (hd : 3≤d) (i : Fin (u+v)) :
    mixedOneHankelDegree u v i≤d+1 := by
  unfold mixedOneHankelDegree
  cases finSumFinEquiv.symm i <;> simp only [mixedKernelDegree_inl,mixedKernelDegree_inr] <;> omega

variable (K : Type*) [Field K]

def mixedOneHankelPairEquiv (u v : ℕ) : Fin (v*(u+v)) ≃ Fin v × Fin (u+v) :=
  finProdFinEquiv.symm

def mixedOneHankelScalarCount (u v d : ℕ) (h : Fin v → ℕ) : ℕ :=
  d+2-∑ l, hankelScalarHeights h (mixedOneHankelDegree u v) (mixedOneHankelPairEquiv u v) d l

set_option maxHeartbeats 800000 in
theorem exists_mixed_one_hankel_upper_witness
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (u v d : ℕ) (hv : 0<v) (hd : 3≤d)
    (hm : Fintype.card m=u+2*v) (hn : Fintype.card n=2*u+3*v)
    (h : Fin v → ℕ) (hh : ∀ j, 0<h j) (hs : ∑ j, h j=3*u+4*v) :
    ∃ (M : Matrix n n (HankelCoefficientField K v (u+v))[X])
      (P : Matrix m n (HankelCoefficientField K v (u+v))[X]),
      DegreeBound M 1 ∧ DegreeBound P 1 ∧ slHilbert M P d ≤
        (∑ i : Fin u ⊕ Fin v, ∑ j, (d-(mixedKernelDegree 1 u v i+1)+1-h j)) +
          mixedOneHankelScalarCount u v d h := by
  let g := mixedOneHankelDegree u v
  let a := universalHankelCoefficients K v (u+v)
  have hg := mixedOneHankelDegree_pos u v
  have hsum : ∑ i, g i=∑ j, h j := (mixedOneHankelDegree_sum u v).trans hs.symm
  obtain ⟨B,hBH,hHB⟩ := universalHankel_inverse K h g hsum.symm
  let F := hankelFrame h g a B
  let ec : Fin u ⊕ Fin v ≃ Fin (u+v) := finSumFinEquiv
  let er := mixedOneHankelRows u v
  let W := F.transpose.submatrix er ec
  have hW (w) (i) : (W w i).natDegree≤mixedKernelDegree 1 u v i+2 := by
    have he := hankelFrame_degree h g a B (ec i) (er w)
    simpa only [W,Matrix.submatrix_apply,Matrix.transpose_apply,g,mixedOneHankelDegree,
      ec,Equiv.symm_apply_apply] using he
  have hWi : Function.Injective W.mulVec := by
    intro x y hxy
    have he : F.transpose *ᵥ (x ∘ ec.symm)=F.transpose *ᵥ (y ∘ ec.symm) := by
      funext w
      have he := congrFun hxy (er.symm w)
      simpa only [W,Matrix.submatrix_mulVec_equiv,Function.comp_apply,Equiv.apply_symm_apply] using he
    have he' := hankelFrame_transpose_injective h g a B hBH hHB hh hg hsum he
    funext i
    simpa only [Function.comp_apply,Equiv.symm_apply_apply] using congrFun he' (ec i)
  have hHil (k : ℕ) : Module.finrank (HankelCoefficientField K v (u+v))
      (polynomialKernelAtDegree W.transpose k)=∑ j, (k+1-h j) := by
    have he := reindex_kernel_hilbert F ec er k
    rw [hankelFrame_kernel_hilbert h g a B hBH hHB hh hg] at he
    exact he
  apply exists_mixed_sl_upper_witness_of_matrix 1 u v d hv (by omega)
    (by omega) (by omega) W hW hWi _ (by simp_rw [hHil])
    (mixedOneHankelScalarCount u v d h)
    (fun q => (∑ l, hankelScalarHeights h g (mixedOneHankelPairEquiv u v) d l)+q.val)
  intro E p hE hp hrel hselect
  have hlift : ∀ i : Fin (u+v), ∃ x : Fin (u+v) ⊕ Fin v → (HankelCoefficientField K v (u+v))[X],
      (∀ w, (x w).natDegree≤d+1-g i) ∧ F *ᵥ x=Pi.single i (-p) := by
    intro i
    let x := fun w => E (ec.symm i) (er.symm w)
    refine ⟨x,?_,?_⟩
    · intro w
      rcases hE (ec.symm i) (er.symm w) with he | ⟨_,he⟩
      · simp only [x,he,natDegree_zero]; omega
      · change (E (ec.symm i) (er.symm w)).natDegree≤_
        change (E (ec.symm i) (er.symm w)).natDegree≤d+1-(mixedKernelDegree 1 u v (ec.symm i)+2)
        omega
    · funext k
      have he := congrFun (congrFun hrel (ec.symm i)) (ec.symm k)
      simp only [Matrix.mul_apply,Matrix.smul_apply,Pi.smul_apply,smul_eq_mul,Matrix.one_apply] at he
      change (∑ w, F k w*x w)=(Pi.single i (-p) : Fin (u+v) → (HankelCoefficientField K v (u+v))[X]) k
      rw [← Equiv.sum_comp er]
      simp only [x,Equiv.symm_apply_apply]
      have he' : (∑ w, F k (er w)*E (ec.symm i) w)=
          (-p)*(if ec.symm i=ec.symm k then 1 else 0) := by
        simpa only [W,Matrix.submatrix_apply,Matrix.transpose_apply,Equiv.apply_symm_apply,mul_comm] using he
      rw [he']
      simp [Pi.single_apply,ec.symm.injective.eq_iff,eq_comm]
  have hz := universalHankel_scalar_selector K h g (mixedOneHankelPairEquiv u v) B hBH hHB
    hh hg hsum d (mixedOneHankelDegree_le u v d hd) (-p) (by simpa using hp) hlift
    (by intro q; simpa only [coeff_neg,neg_eq_zero] using hselect q)
  exact neg_eq_zero.mp hz

end FD56
