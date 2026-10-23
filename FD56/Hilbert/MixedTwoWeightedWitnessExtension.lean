/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MixedTwoSmallWitness
import FD56.Hilbert.MixedTwoAffineScalarWitness

/-! Padding the weighted two-low-column scalar obstruction. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K : Type*} [Field K]

theorem mixedTwoSmallWitness_eval_zero_injective :
    Function.Injective ((mixedTwoSmallWitness (K := K)).map (Polynomial.evalRingHom 0)).mulVec := by
  intro u v h
  funext j
  fin_cases j
  · simpa [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,mixedTwoSmallWitness] using congrFun h (0 : Fin 7)
  · simpa [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,mixedTwoSmallWitness] using congrFun h (1 : Fin 7)
  · simpa [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,mixedTwoSmallWitness] using congrFun h (2 : Fin 7)

theorem mixedTwoSmallWitness_quadratic_row_zero
    (v : Fin 7 → K[X]) (hv : ∀ x, (v x).natDegree ≤ 2)
    (hrel : ∀ z, ∑ x, v x*mixedTwoSmallWitness (K := K) x z=0) : v=0 := by
  let E : Matrix (Fin 3) (Fin 7) K[X] := fun i x => if i=0 then v x else 0
  have hn : (0 : Fin 3) ≠ 2 := by decide
  have hE : ∀ i x, (E i x).natDegree ≤ if i=2 then 1 else 2 := by
    intro i x
    by_cases hi : i=0
    · subst i
      simpa [E,hn] using hv x
    · simp [E,hi]
  have hEG : E*mixedTwoSmallWitness (K := K) = (-(0 : K[X])) • (1 : Matrix (Fin 3) (Fin 3) K[X]) := by
    funext i z
    by_cases hi : i=0 <;> simp [Matrix.mul_apply,E,hi,hrel]
  have h := (mixedTwoSmallWitness_scalar_obstruction E 0 hE hEG).1
  funext x
  simpa [E] using congrFun (congrFun h 0) x

set_option maxHeartbeats 1500000 in
theorem exists_mixed_two_weighted_scalar_witness (u : ℕ) (hu : 2 ≤ u) :
    ∃ G : Matrix (MixedScalarRows 2 (Fin u) (Fin 1)) (Fin u ⊕ Fin 1) K[X],
      (∀ x z, (G x z).natDegree ≤ 4+mixedColumnShift z) ∧
      Function.Injective G.mulVec ∧
      Function.Injective (G.map (Polynomial.evalRingHom 0)).mulVec ∧
      (∀ (v : MixedScalarRows 2 (Fin u) (Fin 1) → K[X]),
        (∀ x, (v x).natDegree ≤ 2) → (∀ z, ∑ x, v x*G x z=0) → v=0) ∧
      ∀ (E : Matrix (Fin u ⊕ Fin 1) (MixedScalarRows 2 (Fin u) (Fin 1)) K[X]) (c : K[X]),
        (∀ i x, (E i x).natDegree ≤ Sum.elim (fun _ => 2) (fun _ => 1) i) →
        E*G=(-c) • 1 → E=0 ∧ c=0 := by
  let W := separatedMonomialColumns (K := K) (Fin (u-2)) 4
  let T := Matrix.fromBlocks (mixedTwoSmallWitness (K := K)) 0 0 W
  have hW0 : Function.Injective (W.map (Polynomial.evalRingHom 0)).mulVec := by
    intro x y hxy
    funext z
    have hrow (j : Fin (u-2)) : Polynomial.eval 0 (W (Sum.inl z) j) = if z=j then 1 else 0 := by
      dsimp [W,separatedMonomialColumns]
      split_ifs <;> simp
    simpa only [Matrix.mulVec,dotProduct,Matrix.map_apply,Polynomial.coe_evalRingHom,
      hrow,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,if_true] using congrFun hxy (Sum.inl z)
  have hTmap : T.map (Polynomial.evalRingHom 0) =
      Matrix.fromBlocks ((mixedTwoSmallWitness (K := K)).map (Polynomial.evalRingHom 0)) 0 0
        (W.map (Polynomial.evalRingHom 0)) := by
    funext x z
    cases x <;> cases z <;> simp [T,Matrix.fromBlocks]
  have hT0 : Function.Injective (T.map (Polynomial.evalRingHom 0)).mulVec := by
    rw [hTmap]
    exact field_block_sum_injective _ _ mixedTwoSmallWitness_eval_zero_injective hW0
  have hTd (x) (z : Fin 3 ⊕ Fin (u-2)) :
      (T x z).natDegree ≤ if z=Sum.inl 2 then 5 else 4 := by
    cases x <;> cases z
    · simpa [T,Matrix.fromBlocks] using mixedTwoSmallWitness_degree (K := K) _ _
    · simp [T,Matrix.fromBlocks]
    · simp [T,Matrix.fromBlocks]
    · simpa [T,Matrix.fromBlocks] using separatedMonomialColumns_degree (K := K) (d := Fin (u-2)) 4 _ _
  have hTk : ∀ (v : Fin 7 ⊕ (Fin (u-2) ⊕ Fin (u-2)) → K[X]),
      (∀ x, (v x).natDegree ≤ 2) → (∀ z, ∑ x, v x*T x z=0) → v=0 :=
    block_sum_row_zero mixedTwoSmallWitness W 2 mixedTwoSmallWitness_quadratic_row_zero
      (separatedMonomialColumns_row_zero 2 4 (by decide))
  have hzero : ∀ (E : Matrix (Fin 3 ⊕ Fin (u-2)) (Fin 7 ⊕ (Fin (u-2) ⊕ Fin (u-2))) K[X])
      (c : K[X]), (∀ i x, (E i x).natDegree ≤ if i=Sum.inl 2 then 1 else 2) →
      E*T=(-c) • 1 → E=0 ∧ c=0 := by
    intro E c hE hrel
    let E₀ := E.submatrix Sum.inl Sum.inl
    have hE₀ : ∀ i x, (E₀ i x).natDegree ≤ if i=2 then 1 else 2 := by
      intro i x
      simpa [E₀] using hE (Sum.inl i) (Sum.inl x)
    have hrel₀ : E₀*mixedTwoSmallWitness (K := K)=(-c) • (1 : Matrix (Fin 3) (Fin 3) K[X]) := by
      funext i z
      simpa [E₀,T,Matrix.mul_apply,Fintype.sum_sum_type,Matrix.fromBlocks,Matrix.one_apply] using
        congrFun (congrFun hrel (Sum.inl i)) (Sum.inl z)
    have hc := (mixedTwoSmallWitness_scalar_obstruction E₀ c hE₀ hrel₀).2
    refine ⟨?_,hc⟩
    rw [hc,neg_zero,zero_smul] at hrel
    funext i
    apply hTk (E i)
    · intro x
      exact (hE i x).trans (by split_ifs <;> omega)
    · intro z
      exact congrFun (congrFun hrel i) z
  let eL : Fin u ≃ Fin 2 ⊕ Fin (u-2) := Fintype.equivOfCardEq (by simp; omega)
  let ep : (Fin 2 ⊕ Fin (u-2)) ⊕ Fin 1 ≃ (Fin 2 ⊕ Fin 1) ⊕ Fin (u-2) :=
    ((Equiv.sumAssoc _ _ _).trans (Equiv.sumCongr (Equiv.refl _) (Equiv.sumComm _ _))).trans
      (Equiv.sumAssoc _ _ _).symm
  let ec : (Fin u ⊕ Fin 1) ≃ Fin 3 ⊕ Fin (u-2) :=
    ((Equiv.sumCongr eL (Equiv.refl _)).trans ep).trans (Equiv.sumCongr finSumFinEquiv (Equiv.refl _))
  let er : MixedScalarRows 2 (Fin u) (Fin 1) ≃ Fin 7 ⊕ (Fin (u-2) ⊕ Fin (u-2)) :=
    Fintype.equivOfCardEq (by simp [MixedScalarRows]; omega)
  have hec : ec (Sum.inr 0)=Sum.inl 2 := by simp [ec,ep,Equiv.sumAssoc,finSumFinEquiv]
  have hlow (z : Fin u) : ec (Sum.inl z) ≠ Sum.inl 2 := by
    rw [← hec]
    exact fun h => Sum.noConfusion (ec.injective h)
  have hweight (z : Fin u ⊕ Fin 1) :
      (if ec z=Sum.inl 2 then 1 else 2) = Sum.elim (fun _ => 2) (fun _ => 1) z := by
    cases z with
    | inl z => simp [hlow]
    | inr z => fin_cases z; simp [hec]
  let G := T.submatrix er ec
  have hG0 : Function.Injective (G.map (Polynomial.evalRingHom 0)).mulVec := by
    intro x y hxy
    have hh : (fun z => x (ec.symm z))=(fun z => y (ec.symm z)) := by
      apply hT0
      funext i
      have h := congrFun hxy (er.symm i)
      change ((T.map (Polynomial.evalRingHom 0)).submatrix er ec *ᵥ x) (er.symm i) =
        ((T.map (Polynomial.evalRingHom 0)).submatrix er ec *ᵥ y) (er.symm i) at h
      simpa only [Matrix.submatrix_mulVec_equiv,Function.comp_apply,Equiv.apply_symm_apply] using h
    funext z
    simpa only [Equiv.symm_apply_apply] using congrFun hh (ec z)
  have hGk : ∀ (v : MixedScalarRows 2 (Fin u) (Fin 1) → K[X]),
      (∀ x, (v x).natDegree ≤ 2) → (∀ z, ∑ x, v x*G x z=0) → v=0 := by
    intro v hv hrel
    have hh : (fun x => v (er.symm x))=0 := by
      apply hTk _ (fun x => hv (er.symm x))
      intro z
      have h := hrel (ec.symm z)
      simpa [G,← er.symm.sum_comp] using h
    funext x
    simpa only [Equiv.symm_apply_apply] using congrFun hh (er x)
  refine ⟨G,?_,polynomial_matrix_injective_of_zero G hG0,hG0,hGk,?_⟩
  · intro x z
    have h := hTd (er x) (ec z)
    cases z with
    | inl z => simpa [G,hlow,mixedColumnShift] using h
    | inr z => fin_cases z; simpa [G,hec,mixedColumnShift] using h
  · intro E c hE hrel
    let E' := E.submatrix ec.symm er.symm
    have hE' : ∀ i x, (E' i x).natDegree ≤ if i=Sum.inl 2 then 1 else 2 := by
      intro i x
      have h := hE (ec.symm i) (er.symm x)
      rw [← hweight,Equiv.apply_symm_apply] at h
      exact h
    have hrel' : E'*T=(-c) • 1 := by
      have hEE : E'.submatrix ec er=E := by funext i z; simp [E']
      change E*T.submatrix er ec=_ at hrel
      rw [← hEE,Matrix.submatrix_mul_equiv] at hrel
      funext i z
      have h := congrFun (congrFun hrel (ec.symm i)) (ec.symm z)
      simpa [Matrix.submatrix_apply,Matrix.smul_apply,Matrix.one_apply,ec.symm.injective.eq_iff] using h
    obtain ⟨hE0,hc0⟩ := hzero E' c hE' hrel'
    refine ⟨?_,hc0⟩
    funext i z
    have h := congrFun (congrFun hE0 (ec i)) (er z)
    simpa [E'] using h

end FD56
