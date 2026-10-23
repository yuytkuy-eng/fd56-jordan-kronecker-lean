/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MixedSLGeneralRealization
import FD56.Hilbert.MixedThreeGenericWitness
import FD56.Hilbert.MixedThreeSLCriticalBound
import FD56.Hilbert.MixedThreeSmallWitness
import FD56.Hilbert.MixedSLCritical
import FD56.Hilbert.GenericKernelExtension

/-! The two critical Hilbert values for mixed quotient three. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem generic_mixed_three_slHilbert_six_upper (u v : ℕ) (hu : 0 < u) (hv : 0 < v)
    (hm : Fintype.card m = 3*(u+v)+v)
    (hn : Fintype.card n = Fintype.card m+(u+v)) (i₀ : n) :
    slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) 6 ≤
      u*(u+3*v)+(8-u*v) := by
  let F := MixedWitnessField K 3 u v
  let W := genericMixedWitness K 3 u v
  have hsize : u+v < 3*(u+v)+v := by omega
  have hW1 : Module.finrank F (polynomialKernelAtDegree W.transpose 1) = 0 := by
    rw [genericMixedWitness_kernel_hilbert 3 u v hsize]
    omega
  have hW2 : Module.finrank F (polynomialKernelAtDegree W.transpose 2) = u+3*v := by
    rw [genericMixedWitness_kernel_hilbert 3 u v hsize]
    omega
  have hsum : (∑ i, Module.finrank F (polynomialKernelAtDegree W.transpose
      (6-(mixedKernelDegree 3 u v i+1)))) = u*(u+3*v) := by
    simp only [Fintype.sum_sum_type,mixedKernelDegree_inl,mixedKernelDegree_inr,
      Nat.reduceAdd,Nat.reduceSub,hW1,hW2,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,smul_eq_mul,mul_zero,add_zero]
  have hz (E : Matrix (Fin u ⊕ Fin v) (MixedScalarRows 3 (Fin u) (Fin v)) F[X])
      (c : F[X])
      (hE : ∀ i j, E i j = 0 ∨ (mixedKernelDegree 3 u v i+1 ≤ 6 ∧
        (E i j).natDegree ≤ 6-(mixedKernelDegree 3 u v i+1)))
      (hc : c.natDegree ≤ 7) (hrel : E * W = (-c) • 1)
      (ht : ∀ j : Fin (8-u*v), c.coeff (u*v+j.val) = 0) : c = 0 := by
    let Eh := E.submatrix Sum.inr id
    have hEh : DegreeBound Eh 1 := by
      intro i j
      rcases hE (Sum.inr i) j with h | ⟨_,h⟩
      · change (E (Sum.inr i) j).natDegree ≤ 1
        rw [h]; simp
      · simpa only [mixedKernelDegree_inr,Nat.reduceAdd,Nat.reduceSub] using h
    have hrelh : Eh * W = (-c) • (mixedScalarHighIdentity :
        Matrix (Fin v) (Fin u ⊕ Fin v) F[X]) := by
      funext i j
      have h := congrArg (fun A : Matrix (Fin u ⊕ Fin v) (Fin u ⊕ Fin v) F[X] =>
        A (Sum.inr i) j) hrel
      simpa [Eh,mixedScalarHighIdentity,Matrix.mul_apply,Matrix.one_apply] using h
    exact (genericMixedThreeWitness_scalar_obstruction (K := K) u v hv Eh c hEh hc hrelh ht).2
  obtain ⟨M,P,hM,hP,hH⟩ := exists_mixed_sl_upper_witness_of_matrix
    3 u v 6 hv (by omega) hm hn W (genericMixedWitness_degree 3 u v)
    (genericMixedWitness_injective 3 u v (by omega) hv) (u*(u+3*v)) hsum
    (8-u*v) (fun j => u*v+j.val) hz
  exact (generic_slHilbert_le_field_witness (algebraMap K F) M P hM hP i₀ 6).trans hH

theorem generic_mixed_three_slHilbert_six (u v : ℕ) (hu : 0 < u) (hv : 0 < v)
    (hm : Fintype.card m = 3*(u+v)+v)
    (hn : Fintype.card n = Fintype.card m+(u+v)) (i₀ : n) :
    slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) 6 =
      u*(u+3*v)+(8-u*v) :=
  le_antisymm (generic_mixed_three_slHilbert_six_upper u v hu hv hm hn i₀)
    (generic_mixed_three_slHilbert_six_lower u v hu hm hn i₀)

def mixedThreeSmallColumnEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2 where
  toFun := Sum.elim (fun _ => 0) (fun _ => 1)
  invFun i := if i=0 then Sum.inl 0 else Sum.inr 0
  left_inv i := by
    cases i with
    | inl i => fin_cases i; rfl
    | inr i => fin_cases i; rfl
  right_inv i := by fin_cases i <;> rfl

theorem mixedThreeSmallWitness_kernel_hilbert (d : ℕ) (hd : d ≤ 1) :
    Module.finrank K (polynomialKernelAtDegree (mixedThreeSmallWitness (K := K)).transpose d) = 0 := by
  have hbot : polynomialKernelAtDegree (mixedThreeSmallWitness (K := K)).transpose d = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    change (mixedThreeSmallWitness (K := K)).transpose *ᵥ (fun j => (x j).val) = 0 at hx
    let E : Matrix (Fin 2) (Fin 7) K[X] := fun i j => if i=0 then (x j).val else 0
    have hE : ∀ i j, (E i j).natDegree ≤ if i=0 then 1 else 0 := by
      intro i j
      by_cases hi : i=0
      · simpa only [E,if_pos hi] using (boundedPoly_degree d (x j)).trans hd
      · simp [E,hi]
    have hrow (j : Fin 2) : ∑ k, (x k).val * mixedThreeSmallWitness k j = 0 := by
      have hh := congrFun hx j
      simpa only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,mul_comm,Pi.zero_apply] using hh
    have hrel : E * mixedThreeSmallWitness = (-(0 : K[X])) • (1 : Matrix (Fin 2) (Fin 2) K[X]) := by
      funext i j
      by_cases hi : i=0 <;> simp [Matrix.mul_apply,E,hi,hrow]
    have hz := (mixedThreeSmallWitness_scalar_obstruction E 0 hE hrel).1
    funext j
    apply Subtype.ext
    simpa [E] using congrFun (congrFun hz 0) j
  rw [hbot,finrank_bot]

theorem exists_mixed_three_small_sl_degree_five_witness
    (hm : Fintype.card m = 7) (hn : Fintype.card n = 9) :
    ∃ (M : Matrix n n K[X]) (P : Matrix m n K[X]),
      DegreeBound M 1 ∧ DegreeBound P 1 ∧ slHilbert M P 5 ≤ 0 := by
  let er : MixedScalarRows 3 (Fin 1) (Fin 1) ≃ Fin 7 :=
    Fintype.equivOfCardEq (by simp [MixedScalarRows])
  let ec := mixedThreeSmallColumnEquiv
  let G := mixedThreeSmallWitness (K := K)
  let W := G.submatrix er ec
  have hW : ∀ x j, (W x j).natDegree ≤ mixedKernelDegree 3 1 1 j+2 := by
    intro x j
    have hh := mixedThreeSmallWitness_degree (K := K) (er x) (ec j)
    cases j <;> simpa [ec,mixedThreeSmallColumnEquiv] using hh
  have hWi : Function.Injective W.mulVec := by
    intro x y h
    have hh : G *ᵥ (x ∘ ec.symm) = G *ᵥ (y ∘ ec.symm) := by
      funext i
      have hi := congrFun h (er.symm i)
      simpa only [W,Matrix.submatrix_mulVec_equiv,Function.comp_apply,Equiv.apply_symm_apply] using hi
    have he := mixedThreeSmallWitness_injective hh
    funext j
    simpa using congrFun he (ec j)
  have hH : (∑ i, Module.finrank K (polynomialKernelAtDegree W.transpose
      (5-(mixedKernelDegree 3 1 1 i+1)))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [show W.transpose = G.transpose.submatrix ec er from rfl,reindex_kernel_hilbert]
    apply mixedThreeSmallWitness_kernel_hilbert
    cases i <;> simp
  have hz (E : Matrix (Fin 1 ⊕ Fin 1) (MixedScalarRows 3 (Fin 1) (Fin 1)) K[X])
      (c : K[X])
      (hE : ∀ i j, E i j = 0 ∨ (mixedKernelDegree 3 1 1 i+1 ≤ 5 ∧
        (E i j).natDegree ≤ 5-(mixedKernelDegree 3 1 1 i+1)))
      (_hc : c.natDegree ≤ 6) (hrel : E * W = (-c) • 1)
      (_ht : ∀ j : Fin 0, c.coeff (Fin.elim0 j) = 0) : c = 0 := by
    let E' := E.submatrix ec.symm er.symm
    have hbounds (i : Fin 1 ⊕ Fin 1) (j : MixedScalarRows 3 (Fin 1) (Fin 1)) :
        (E i j).natDegree ≤ 5-(mixedKernelDegree 3 1 1 i+1) := by
      rcases hE i j with hz | ⟨_,hh⟩
      · rw [hz]; simp
      · exact hh
    have hE' : ∀ i j, (E' i j).natDegree ≤ if i=0 then 1 else 0 := by
      intro i j
      fin_cases i
      · change (E (Sum.inl 0) (er.symm j)).natDegree ≤ 1
        simpa only [mixedKernelDegree_inl] using hbounds (Sum.inl 0) (er.symm j)
      · change (E (Sum.inr 0) (er.symm j)).natDegree ≤ 0
        simpa only [mixedKernelDegree_inr] using hbounds (Sum.inr 0) (er.symm j)
    have hrel' : E' * G = (-c) • (1 : Matrix (Fin 2) (Fin 2) K[X]) := by
      have he : E'.submatrix ec er = E := by funext i j; simp [E']
      change E * G.submatrix er ec = _ at hrel
      rw [← he,Matrix.submatrix_mul_equiv] at hrel
      funext i j
      have hh := congrFun (congrFun hrel (ec.symm i)) (ec.symm j)
      simpa [Matrix.submatrix_apply,Matrix.smul_apply,Matrix.one_apply] using hh
    exact (mixedThreeSmallWitness_scalar_obstruction E' c hE' hrel').2
  exact exists_mixed_sl_upper_witness_of_matrix 3 1 1 5 (by omega) (by omega)
    (by simpa using hm) (by omega) W hW hWi 0 hH 0 Fin.elim0 hz

theorem generic_mixed_three_small_slHilbert_five
    (hm : Fintype.card m = 7) (hn : Fintype.card n = 9) (i₀ : n) :
    slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) 5 = 0 := by
  obtain ⟨M,P,hM,hP,hH⟩ := exists_mixed_three_small_sl_degree_five_witness (K := K) hm hn
  exact Nat.eq_zero_of_le_zero ((generic_slHilbert_le_witness M P hM hP i₀ 5).trans hH)

theorem generic_mixed_three_slHilbert_five (u v : ℕ) (hu : 0 < u) (hv : 0 < v)
    (hm : Fintype.card m = 3*(u+v)+v)
    (hn : Fintype.card n = Fintype.card m+(u+v)) (i₀ : n) :
    slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) 5 = 0 := by
  by_cases hp : 3 ≤ (u+v)*v
  · exact generic_mixed_three_slHilbert_five_of_product u v hu hv hp hm hn i₀
  · have huv : u=1 ∧ v=1 := by constructor <;> nlinarith
    rcases huv with ⟨rfl,rfl⟩
    exact generic_mixed_three_small_slHilbert_five (by omega) (by omega) i₀

end FD56
