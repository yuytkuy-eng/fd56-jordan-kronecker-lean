/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.UniformCubicCompletion
import FD56.Hilbert.MixedSLGeneralRealization
import FD56.Hilbert.GenericKernelBound

/-! Affine realization of the low-degree scalar bounds from cubic completions. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K n m a r q t : Type*} [Field K] [Fintype n] [Fintype m]
  [Fintype a] [Fintype r] [Fintype t] [Fintype q]
  [DecidableEq n] [DecidableEq m] [DecidableEq a] [DecidableEq r] [DecidableEq q]

theorem generic_mixed_uniform_upper_of_completion
    {alpha : r → ℕ} {b : ℕ} {W : Matrix q q K[X]}
    (C : UniformCubicCompletion (m := a) alpha b W) (u v d : ℕ) (hv : 0<v)
    (hm : Fintype.card m=u+2*v) (hn : Fintype.card n=2*u+3*v)
    (hrow : Fintype.card a=u+2*v)
    (e : r ≃ Fin u ⊕ Fin v) (he : ∀ j, mixedKernelDegree 1 u v (e j)=alpha j)
    (hd : 3≤d) (hdb : d≤b+1) (f : t → ℕ)
    (hzero : C.ScalarSelector d f) (i₀ : n) :
    slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) d≤Fintype.card t := by
  classical
  let er : MixedScalarRows 1 (Fin u) (Fin v) ≃ a := Fintype.equivOfCardEq (by
    rw [mixedScalarRows_card,hrow]
    simp
    omega)
  let G := C.G.submatrix er e.symm
  have he' (j : Fin u ⊕ Fin v) : alpha (e.symm j)=mixedKernelDegree 1 u v j := by
    simpa using (he (e.symm j)).symm
  have hG : ∀ x j, (G x j).natDegree≤mixedKernelDegree 1 u v j+2 := by
    intro x j
    simpa only [he'] using C.gDegree (er x) (e.symm j)
  have hGi : Function.Injective G.mulVec := by
    intro x y h
    have hh : C.G *ᵥ (x ∘ e)=C.G *ᵥ (y ∘ e) := by
      funext i
      have hz := congrFun h (er.symm i)
      simpa [G, Matrix.submatrix_mulVec_equiv, Function.comp_def] using hz
    have hh' := C.injective hh
    funext j
    simpa using congrFun hh' (e.symm j)
  have hGH (k : ℕ) : Module.finrank K (polynomialKernelAtDegree G.transpose k)=
      Module.finrank K (polynomialKernelAtDegree C.G.transpose k) :=
    reindex_kernel_hilbert C.G.transpose e.symm er k
  have hH : (∑ i, Module.finrank K (polynomialKernelAtDegree G.transpose
      (d-(mixedKernelDegree 1 u v i+1))))=0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [hGH]
    apply C.kernel_hilbert_zero
    cases i <;> simp only [mixedKernelDegree_inl,mixedKernelDegree_inr,Nat.reduceAdd] <;> omega
  let ef : Fin (Fintype.card t) ≃ t := (Fintype.equivFin t).symm
  obtain ⟨M,P,hM,hP,hbound⟩ := exists_mixed_sl_upper_witness_of_matrix (K := K)
    (n := n) (m := m) 1 u v d hv hd
    (by simp; omega) (by omega) G hG hGi 0 hH (Fintype.card t) (fun j => f (ef j))
    (by
      intro E c hE hc hrel hsel
      let E' := E.submatrix e er.symm
      have hE' : ∀ i x, (E' i x).natDegree≤d-(alpha i+1) := by
        intro i x
        rcases hE (e i) (er.symm x) with hz | ⟨_,hh⟩
        · change (E (e i) (er.symm x)).natDegree≤_
          simp [hz]
        · simpa only [he] using hh
      have hCG : C.G=G.submatrix er.symm e := by
        funext x j
        simp [G]
      have hrel' : E'*C.G=(-c) • (1 : Matrix r r K[X]) := by
        calc
          E'*C.G = (E*G).submatrix e e := by
            rw [hCG]
            exact Matrix.submatrix_mul_equiv E G e er.symm e
          _ = (-c) • 1 := by
            rw [hrel]
            funext i j
            simp [Matrix.submatrix,Matrix.smul_apply,Matrix.one_apply,e.injective.eq_iff]
      exact hzero E' c hE' hc hrel' (by
        intro j
        simpa [ef] using hsel (ef.symm j)))
  exact (generic_slHilbert_le_witness M P hM hP i₀ d).trans (by simpa using hbound)

theorem generic_mixed_uniform_zero_of_completion
    {alpha : r → ℕ} {b : ℕ} {W : Matrix q q K[X]}
    (C : UniformCubicCompletion (m := a) alpha b W) (u v d : ℕ) (hv : 0<v)
    (hm : Fintype.card m=u+2*v) (hn : Fintype.card n=2*u+3*v)
    (hrow : Fintype.card a=u+2*v)
    (e : r ≃ Fin u ⊕ Fin v) (he : ∀ j, mixedKernelDegree 1 u v (e j)=alpha j)
    (hd : 3≤d) (hdb : d≤b+1)
    (hzero : C.ScalarZero d) (i₀ : n) :
    slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) d=0 := by
  apply Nat.eq_zero_of_le_zero
  have hh := generic_mixed_uniform_upper_of_completion C u v d hv hm hn hrow e he hd hdb
    (fun j : Fin 0 => j.elim0) (fun E c hE hc hr _ => hzero E c hE hc hr) i₀
  simpa using hh

end FD56
