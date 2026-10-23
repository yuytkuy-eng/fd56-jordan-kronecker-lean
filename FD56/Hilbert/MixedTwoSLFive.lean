/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MixedTwoSLRealization
import FD56.Hilbert.MixedTwoAffineScalarWitness
import FD56.Hilbert.MixedTwoSingleScalarWitness
import FD56.Hilbert.MixedTwoWeightedWitnessExtension

/-! The degree-five mixed SL scalar correction. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem genericMixedTwoWitness_affine_scalar_zero (u v : ℕ) (hu : 0 < u) (hv : 2 ≤ v)
    (E : Matrix (Fin v) (MixedScalarRows 2 (Fin u) (Fin v)) (MixedWitnessField K 2 u v)[X])
    (c : (MixedWitnessField K 2 u v)[X]) (hE : DegreeBound E 1) (hc : c.natDegree ≤ 6)
    (hrel : E * genericMixedWitness K 2 u v = (-c) •
      (mixedScalarHighIdentity : Matrix (Fin v) (Fin u ⊕ Fin v) (MixedWitnessField K 2 u v)[X])) :
    c = 0 := by
  obtain ⟨W,hW,_,_,hz⟩ := exists_mixed_two_affine_scalar_witness (K := K) u v hu hv
  have hWe : ∀ x j, (W x j).natDegree ≤ mixedKernelDegree 2 u v j+2 := by
    intro x j
    have h := hW x j
    cases j <;> simpa [mixedKernelDegree,mixedColumnShift] using h
  exact (genericMixedWitness_scalar_obstruction_of_witness 2 u v 1 0 Fin.elim0
    (fun j => Fin.elim0 j) W hWe (fun E c hE hrel _ => hz E c hE hrel)
    E c hE hc hrel (fun j => Fin.elim0 j)).2

theorem generic_mixed_two_slHilbert_five_upper_of_scalar_selector
    (u v : ℕ) (hu : 0 < u) (hv : 0 < v)
    (hm : Fintype.card m = 2*(u+v)+v)
    (hn : Fintype.card n = Fintype.card m+(u+v)) (i₀ : n)
    (t : ℕ) (f : Fin t → ℕ)
    (hscalar : ∀ (E : Matrix (Fin v) (MixedScalarRows 2 (Fin u) (Fin v))
      (MixedWitnessField K 2 u v)[X]) (c : (MixedWitnessField K 2 u v)[X]),
      DegreeBound E 1 → c.natDegree ≤ 6 →
      E * genericMixedWitness K 2 u v = (-c) •
        (mixedScalarHighIdentity : Matrix (Fin v) (Fin u ⊕ Fin v) (MixedWitnessField K 2 u v)[X]) →
      (∀ j, c.coeff (f j) = 0) → c = 0) :
    slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) 5 ≤ u*(v-u)+t := by
  let F := MixedWitnessField K 2 u v
  let W := genericMixedWitness K 2 u v
  have hsize : u+v < 2*(u+v)+v := by omega
  have hW1 : Module.finrank F (polynomialKernelAtDegree W.transpose 1) = 0 := by
    rw [genericMixedWitness_kernel_hilbert 2 u v hsize]
    omega
  have hW2 : Module.finrank F (polynomialKernelAtDegree W.transpose 2) = v-u := by
    rw [genericMixedWitness_kernel_hilbert 2 u v hsize]
    omega
  have hsum : (∑ i, Module.finrank F (polynomialKernelAtDegree W.transpose
      (5-(mixedKernelDegree 2 u v i+1)))) = u*(v-u) := by
    simp only [Fintype.sum_sum_type,mixedKernelDegree_inl,mixedKernelDegree_inr,
      Nat.reduceAdd,Nat.reduceSub,hW1,hW2,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,smul_eq_mul,mul_zero,add_zero]
  have hz (E : Matrix (Fin u ⊕ Fin v) (MixedScalarRows 2 (Fin u) (Fin v)) F[X])
      (c : F[X])
      (hE : ∀ i j, E i j = 0 ∨ (mixedKernelDegree 2 u v i+1 ≤ 5 ∧
        (E i j).natDegree ≤ 5-(mixedKernelDegree 2 u v i+1)))
      (hc : c.natDegree ≤ 6) (hrel : E * W = (-c) • 1)
      (ht : ∀ j, c.coeff (f j) = 0) : c = 0 := by
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
    exact hscalar Eh c hEh hc hrelh ht
  obtain ⟨M,P,hM,hP,hH⟩ := exists_mixed_sl_upper_witness_of_matrix
    2 u v 5 hv (by omega) hm hn W (genericMixedWitness_degree 2 u v)
    (genericMixedWitness_injective 2 u v (by omega) hv) (u*(v-u)) hsum t f hz
  exact (generic_slHilbert_le_field_witness (algebraMap K F) M P hM hP i₀ 5).trans hH

theorem generic_mixed_two_slHilbert_five_of_two_le (u v : ℕ) (hu : 0 < u) (hv : 2 ≤ v)
    (hm : Fintype.card m = 2*(u+v)+v)
    (hn : Fintype.card n = Fintype.card m+(u+v)) (i₀ : n) :
    slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) 5 = u*(v-u) := by
  apply le_antisymm
  · exact (generic_mixed_two_slHilbert_five_upper_of_scalar_selector u v hu (by omega)
      hm hn i₀ 0 Fin.elim0
      (fun E c hE hc hrel _ => genericMixedTwoWitness_affine_scalar_zero u v hu hv E c hE hc hrel)).trans_eq
      (Nat.add_zero _)
  · have hmn : Fintype.card m < Fintype.card n := by omega
    have hnm : Fintype.card n < 2*Fintype.card m := by omega
    have hh := (generic_middle_slHilbert_bounds (K := K) i₀ hmn hnm 5).1
    rwa [generic_mixed_two_glHilbert_five u v hu hm hn] at hh

theorem generic_mixed_two_one_one_slHilbert_five_lower
    (hm : Fintype.card m = 5) (hn : Fintype.card n = 7) (i₀ : n) :
    4 ≤ slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) 5 := by
  letI : Nonempty n := ⟨i₀⟩
  have hmn : Fintype.card m < Fintype.card n := by omega
  obtain ⟨B,hB,hBL⟩ := generic_mixed_kernel_basis (K := K) (n := n) (m := m) 2 1 1
    (by omega) (by omega) (by omega)
  obtain ⟨R,_,hPR⟩ := generic_affine_rows_right_inverse_of_sizes K m n (by omega) hmn
  have hPL := matrix_transpose_injective_of_surjective _
    (generic_affine_rows_leading_surjective K m n hmn.le)
  have hh := weighted_middle_slHilbert_lower _ _ B R hPR
    (mixedKernelDegree 2 1 1) (Sum.elim (fun _ => 2) (fun _ => 1)) 5
    (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m) hB hBL hPL
    (by intro i; cases i <;> simp) (by intro i; cases i <;> simp) (Sum.inl 0)
  simpa only [Fintype.sum_sum_type,mixedKernelDegree_inl,mixedKernelDegree_inr,
    Sum.elim_inl,Sum.elim_inr,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    smul_eq_mul,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,hm] using hh

theorem generic_mixed_two_one_one_slHilbert_five
    (hm : Fintype.card m = 5) (hn : Fintype.card n = 7) (i₀ : n) :
    slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) 5 = 4 := by
  apply le_antisymm
  · have hWe : ∀ x j, (mixedTwoSingleScalarWitness (K := K) x j).natDegree ≤
        mixedKernelDegree 2 1 1 j+2 := by
      intro x j
      have h := mixedTwoSingleScalarWitness_degree (K := K) x j
      cases j <;> simpa [mixedKernelDegree,mixedColumnShift] using h
    have hh := generic_mixed_two_slHilbert_five_upper_of_scalar_selector (K := K)
      (n := n) (m := m) 1 1 (by omega) (by omega) (by omega) (by omega) i₀ 4
      (fun j => j.val) (by
        intro E c hE hc hrel ht
        exact (genericMixedWitness_scalar_obstruction_of_witness 2 1 1 1 4
          (fun j => j.val) (fun j => by have := j.isLt; dsimp; omega)
          mixedTwoSingleScalarWitness hWe mixedTwoSingleScalarWitness_scalar_obstruction
          E c hE hc hrel ht).2)
    simpa using hh
  · exact generic_mixed_two_one_one_slHilbert_five_lower hm hn i₀

theorem mixed_two_left_kernel_zero_of_relation_zero (u : ℕ) (hu : 0 < u)
    (W : Matrix (MixedScalarRows 2 (Fin u) (Fin 1)) (Fin u ⊕ Fin 1) K[X])
    (hzero : ∀ (E : Matrix (Fin u ⊕ Fin 1) (MixedScalarRows 2 (Fin u) (Fin 1)) K[X])
      (c : K[X]),
      (∀ i j, (E i j).natDegree ≤ Sum.elim (fun _ => 2) (fun _ => 1) i) →
      E * W = (-c) • 1 → E = 0 ∧ c = 0)
    (d : ℕ) (hd : d ≤ 2) :
    Module.finrank K (polynomialKernelAtDegree W.transpose d) = 0 := by
  have hbot : polynomialKernelAtDegree W.transpose d = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    change W.transpose *ᵥ (fun j => (x j).val) = 0 at hx
    let p : Fin u ⊕ Fin 1 := Sum.inl ⟨0,hu⟩
    let E : Matrix (Fin u ⊕ Fin 1) (MixedScalarRows 2 (Fin u) (Fin 1)) K[X] :=
      fun i j => if i=p then (x j).val else 0
    have hE : ∀ i j, (E i j).natDegree ≤ Sum.elim (fun _ => 2) (fun _ => 1) i := by
      intro i j
      by_cases hi : i=p
      · subst i
        simpa only [E,if_pos rfl,p,Sum.elim_inl] using (boundedPoly_degree d (x j)).trans hd
      · simp [E,hi]
    have hrow (j : Fin u ⊕ Fin 1) : ∑ k, (x k).val * W k j = 0 := by
      have hh := congrFun hx j
      simpa only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,mul_comm,Pi.zero_apply] using hh
    have hrel : E * W = (-(0 : K[X])) • (1 : Matrix (Fin u ⊕ Fin 1) (Fin u ⊕ Fin 1) K[X]) := by
      funext i j
      by_cases hi : i=p <;> simp [Matrix.mul_apply,E,hi,hrow]
    have hz := (hzero E 0 hE hrel).1
    funext j
    apply Subtype.ext
    simpa [E] using congrFun (congrFun hz p) j
  rw [hbot,finrank_bot]

theorem generic_mixed_two_single_high_slHilbert_five_of_matrix (u : ℕ) (hu : 0 < u)
    (hm : Fintype.card m = 2*(u+1)+1)
    (hn : Fintype.card n = Fintype.card m+(u+1)) (i₀ : n)
    (W : Matrix (MixedScalarRows 2 (Fin u) (Fin 1)) (Fin u ⊕ Fin 1) K[X])
    (hW : ∀ x j, (W x j).natDegree ≤ mixedKernelDegree 2 u 1 j+2)
    (hWi : Function.Injective W.mulVec)
    (hzero : ∀ (E : Matrix (Fin u ⊕ Fin 1) (MixedScalarRows 2 (Fin u) (Fin 1)) K[X])
      (c : K[X]),
      (∀ i j, (E i j).natDegree ≤ Sum.elim (fun _ => 2) (fun _ => 1) i) →
      E * W = (-c) • 1 → E = 0 ∧ c = 0) :
    slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) 5 = 0 := by
  have hsum : (∑ i, Module.finrank K (polynomialKernelAtDegree W.transpose
      (5-(mixedKernelDegree 2 u 1 i+1)))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    apply mixed_two_left_kernel_zero_of_relation_zero u hu W hzero
    cases i <;> simp
  have hz (E : Matrix (Fin u ⊕ Fin 1) (MixedScalarRows 2 (Fin u) (Fin 1)) K[X])
      (c : K[X])
      (hE : ∀ i j, E i j = 0 ∨ (mixedKernelDegree 2 u 1 i+1 ≤ 5 ∧
        (E i j).natDegree ≤ 5-(mixedKernelDegree 2 u 1 i+1)))
      (_hc : c.natDegree ≤ 6) (hrel : E * W = (-c) • 1)
      (_ht : ∀ j : Fin 0, c.coeff (Fin.elim0 j) = 0) : c = 0 := by
    apply (hzero E c ?_ hrel).2
    intro i j
    rcases hE i j with he | ⟨_,he⟩
    · rw [he]; simp
    · cases i <;> simpa only [mixedKernelDegree_inl,mixedKernelDegree_inr,
        Sum.elim_inl,Sum.elim_inr,Nat.reduceAdd,Nat.reduceSub] using he
  obtain ⟨M,P,hM,hP,hH⟩ := exists_mixed_sl_upper_witness_of_matrix
    2 u 1 5 (by omega) (by omega) hm hn W hW hWi 0 hsum 0 Fin.elim0 hz
  apply Nat.eq_zero_of_le_zero
  exact (generic_slHilbert_le_witness M P hM hP i₀ 5).trans hH

theorem generic_mixed_two_slHilbert_five_le (u v : ℕ) (hu : 0 < u) (hv : 0 < v)
    (huv : u ≤ v) (hm : Fintype.card m = 2*(u+v)+v)
    (hn : Fintype.card n = Fintype.card m+(u+v)) (i₀ : n) :
    slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) 5 =
      u*(v-u)+(7-v*(2*u+v)) := by
  by_cases hv1 : v=1
  · subst v
    have hu1 : u=1 := by omega
    subst u
    simpa using generic_mixed_two_one_one_slHilbert_five (K := K)
      (by omega : Fintype.card m=5) (by omega : Fintype.card n=7) i₀
  · have hv2 : 2 ≤ v := by omega
    rw [generic_mixed_two_slHilbert_five_of_two_le u v hu hv2 hm hn i₀]
    have ht : 7-v*(2*u+v)=0 := by
      apply Nat.sub_eq_zero_of_le
      nlinarith
    rw [ht,add_zero]

theorem generic_mixed_two_single_high_slHilbert_five (u : ℕ) (hu : 2 ≤ u)
    (hm : Fintype.card m = 2*(u+1)+1)
    (hn : Fintype.card n = Fintype.card m+(u+1)) (i₀ : n) :
    slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) 5 = 0 := by
  obtain ⟨W,hW,hWi,_,_,hz⟩ := exists_mixed_two_weighted_scalar_witness (K := K) u hu
  apply generic_mixed_two_single_high_slHilbert_five_of_matrix u (by omega) hm hn i₀ W _ hWi hz
  intro x j
  have hh := hW x j
  cases j <;> simpa [mixedKernelDegree,mixedColumnShift] using hh

theorem generic_mixed_two_slHilbert_five_gt (u v : ℕ) (hu : 0 < u) (hv : 0 < v)
    (hvu : v < u) (hm : Fintype.card m = 2*(u+v)+v)
    (hn : Fintype.card n = Fintype.card m+(u+v)) (i₀ : n) :
    slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) 5 = 0 := by
  by_cases hv1 : v=1
  · subst v
    exact generic_mixed_two_single_high_slHilbert_five u (by omega) hm hn i₀
  · rw [generic_mixed_two_slHilbert_five_of_two_le u v hu (by omega) hm hn i₀,
      Nat.sub_eq_zero_of_le hvu.le,mul_zero]

end FD56
