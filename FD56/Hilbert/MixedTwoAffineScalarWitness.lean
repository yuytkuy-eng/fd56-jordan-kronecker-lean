/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.FamilySLPartialWitness
import FD56.Hilbert.MixedScalarWitness

/-! Extending the small affine mixed scalar witness by separated columns. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K a b c d h j : Type*} [Field K]
  [Fintype a] [Fintype b] [Fintype c] [Fintype d] [Fintype h] [Fintype j]
  [DecidableEq a] [DecidableEq b] [DecidableEq c] [DecidableEq d]
  [DecidableEq h] [DecidableEq j]

omit [Fintype b] [Fintype h] [DecidableEq a] [DecidableEq h] in
theorem bounded_row_zero_of_partial_scalar_obstruction
    (G : Matrix a b K[X]) (e : h → b) (k : ℕ) (i₀ : h)
    (hzero : ∀ (E : Matrix h a K[X]) (p : K[X]), DegreeBound E k →
      E * G = (-p) • (fun i j => if e i=j then 1 else 0 : Matrix h b K[X]) → E=0 ∧ p=0)
    (v : a → K[X]) (hv : ∀ x, (v x).natDegree ≤ k)
    (hrel : ∀ z, ∑ x, v x*G x z=0) : v=0 := by
  classical
  let E : Matrix h a K[X] := fun i x => if i=i₀ then v x else 0
  have hE : DegreeBound E k := by intro i x; by_cases hi : i=i₀ <;> simp [E,hi,hv]
  have hEG : E*G = (-(0 : K[X])) • (fun i j => if e i=j then 1 else 0 : Matrix h b K[X]) := by
    funext i z
    by_cases hi : i=i₀ <;> simp [Matrix.mul_apply,E,hi,hrel]
  have hh := (hzero E 0 hE hEG).1
  funext x
  simpa [E] using congrFun (congrFun hh i₀) x

omit [Fintype b] [Fintype d] [Fintype h] [Fintype j]
  [DecidableEq a] [DecidableEq c] [DecidableEq h] [DecidableEq j] in
theorem block_sum_partial_scalar_obstruction
    (G : Matrix a b K[X]) (W : Matrix c d K[X]) (e : h → b) (g : j → d)
    (k : ℕ) (i₀ : h)
    (hzero : ∀ (E : Matrix h a K[X]) (p : K[X]), DegreeBound E k →
      E*G = (-p) • (fun i z => if e i=z then 1 else 0 : Matrix h b K[X]) → E=0 ∧ p=0)
    (hW : ∀ (v : c → K[X]), (∀ x, (v x).natDegree ≤ k) →
      (∀ z, ∑ x, v x*W x z=0) → v=0)
    (E : Matrix (h ⊕ j) (a ⊕ c) K[X]) (p : K[X]) (hE : DegreeBound E k)
    (hrel : E * Matrix.fromBlocks G 0 0 W = (-p) •
      (fun i z => if Sum.map e g i=z then 1 else 0 : Matrix (h ⊕ j) (b ⊕ d) K[X])) :
    E=0 ∧ p=0 := by
  let E₀ := E.submatrix Sum.inl Sum.inl
  have hE₀ : DegreeBound E₀ k := fun i x => hE (Sum.inl i) (Sum.inl x)
  have hrel₀ : E₀*G = (-p) • (fun i z => if e i=z then 1 else 0 : Matrix h b K[X]) := by
    funext i z
    simpa [E₀,Matrix.mul_apply,Fintype.sum_sum_type,Matrix.fromBlocks] using
      congrFun (congrFun hrel (Sum.inl i)) (Sum.inl z)
  have hp := (hzero E₀ p hE₀ hrel₀).2
  rw [hp,neg_zero,zero_smul] at hrel
  refine ⟨?_,hp⟩
  have hleft (i : h ⊕ j) : (fun x => E i (Sum.inl x))=0 := by
    apply bounded_row_zero_of_partial_scalar_obstruction G e k i₀ hzero _ (fun x => hE i (Sum.inl x))
    intro z
    simpa [Matrix.mul_apply,Fintype.sum_sum_type,Matrix.fromBlocks] using
      congrFun (congrFun hrel i) (Sum.inl z)
  have hright (i : h ⊕ j) : (fun x => E i (Sum.inr x))=0 := by
    apply hW _ (fun x => hE i (Sum.inr x))
    intro z
    simpa [Matrix.mul_apply,Fintype.sum_sum_type,Matrix.fromBlocks] using
      congrFun (congrFun hrel i) (Sum.inr z)
  funext i x
  cases x with
  | inl x => exact congrFun (hleft i) x
  | inr x => exact congrFun (hright i) x

def threeSeparatedColumns (d : Type*) [DecidableEq d] : Matrix (Fin 3 × d) d K[X] :=
  fun x z => if x.2=z then X^(2*x.1.val) else 0

omit [Fintype d] in
theorem threeSeparatedColumns_degree : DegreeBound (threeSeparatedColumns (K := K) d) 4 := by
  intro x z
  simp only [threeSeparatedColumns]
  split_ifs
  · exact (natDegree_X_pow_le _).trans (by have := x.1.isLt; omega)
  · simp

theorem threeSeparatedColumns_eval_zero_injective :
    Function.Injective ((threeSeparatedColumns (K := K) d).map (Polynomial.evalRingHom 0)).mulVec := by
  intro u v h
  funext z
  have hrow (j : d) : Polynomial.eval 0 (threeSeparatedColumns (K := K) d (0,z) j) =
      if z=j then 1 else 0 := by
    simp only [threeSeparatedColumns,Fin.val_zero,mul_zero,pow_zero]
    split_ifs <;> simp
  simpa only [Matrix.mulVec,dotProduct,Matrix.map_apply,Polynomial.coe_evalRingHom,
    hrow,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,if_true] using congrFun h ((0 : Fin 3),z)

theorem threeSeparatedColumns_affine_row_zero
    (v : Fin 3 × d → K[X]) (hv : ∀ x, (v x).natDegree ≤ 1)
    (hrel : ∀ z, ∑ x, v x*threeSeparatedColumns (K := K) d x z=0) : v=0 := by
  have hc (x : Fin 3 × d) (k : ℕ) (hk : 1<k) : (v x).coeff k=0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hv x) hk)
  have heq (z : d) : v (0,z)+v (1,z)*X^2+v (2,z)*X^4=0 := by
    simpa [threeSeparatedColumns,Fintype.sum_prod_type,Fin.sum_univ_succ,mul_ite,add_assoc] using hrel z
  have hcoeff (l : Fin 3) (q : Fin 2) (z : d) : (v (l,z)).coeff q.val=0 := by
    have h := congrArg (fun p : K[X] => p.coeff (2*l.val+q.val)) (heq z)
    fin_cases l <;> fin_cases q <;> simpa [coeff_add,coeff_mul_X_pow',hc] using h
  funext x
  rw [eq_X_add_C_of_natDegree_le_one (hv x)]
  have h0 := hcoeff x.1 0 x.2
  have h1 := hcoeff x.1 1 x.2
  simp only [Fin.val_zero] at h0
  simp only [Fin.val_one] at h1
  simp [h0,h1]

omit [Fintype b] [Fintype d] [DecidableEq a] [DecidableEq b] [DecidableEq c] [DecidableEq d] in
theorem block_sum_row_zero (G : Matrix a b K[X]) (W : Matrix c d K[X]) (k : ℕ)
    (hG : ∀ (v : a → K[X]), (∀ x, (v x).natDegree ≤ k) → (∀ z, ∑ x, v x*G x z=0) → v=0)
    (hW : ∀ (v : c → K[X]), (∀ x, (v x).natDegree ≤ k) → (∀ z, ∑ x, v x*W x z=0) → v=0)
    (v : a ⊕ c → K[X]) (hv : ∀ x, (v x).natDegree ≤ k)
    (hrel : ∀ z, ∑ x, v x*(Matrix.fromBlocks G 0 0 W) x z=0) : v=0 := by
  have hl : (fun x => v (Sum.inl x))=0 := by
    apply hG _ (fun x => hv (Sum.inl x))
    intro z
    simpa [Fintype.sum_sum_type,Matrix.fromBlocks] using hrel (Sum.inl z)
  have hr : (fun x => v (Sum.inr x))=0 := by
    apply hW _ (fun x => hv (Sum.inr x))
    intro z
    simpa [Fintype.sum_sum_type,Matrix.fromBlocks] using hrel (Sum.inr z)
  funext x
  cases x with
  | inl x => exact congrFun hl x
  | inr x => exact congrFun hr x

omit [Fintype a] [Fintype c] [DecidableEq a] [DecidableEq b] [DecidableEq c] [DecidableEq d] in
theorem field_block_sum_injective (A : Matrix a b K) (B : Matrix c d K)
    (hA : Function.Injective A.mulVec) (hB : Function.Injective B.mulVec) :
    Function.Injective (Matrix.fromBlocks A 0 0 B).mulVec := by
  intro u v h
  have hl : (fun i => u (Sum.inl i)) = (fun i => v (Sum.inl i)) := by
    apply hA
    funext i
    simpa [Matrix.mulVec,dotProduct,Fintype.sum_sum_type,Matrix.fromBlocks] using congrFun h (Sum.inl i)
  have hr : (fun i => u (Sum.inr i)) = (fun i => v (Sum.inr i)) := by
    apply hB
    funext i
    simpa [Matrix.mulVec,dotProduct,Fintype.sum_sum_type,Matrix.fromBlocks] using congrFun h (Sum.inr i)
  funext i
  cases i with
  | inl i => exact congrFun hl i
  | inr i => exact congrFun hr i

set_option maxHeartbeats 2000000 in
theorem exists_mixed_two_affine_scalar_witness (u v : ℕ) (hu : 0 < u) (hv : 2 ≤ v) :
    ∃ G : Matrix (MixedScalarRows 2 (Fin u) (Fin v)) (Fin u ⊕ Fin v) K[X],
      (∀ x z, (G x z).natDegree ≤ 4+mixedColumnShift z) ∧
      Function.Injective G.mulVec ∧
      Function.Injective (G.map (Polynomial.evalRingHom 0)).mulVec ∧
      ∀ (E : Matrix (Fin v) (MixedScalarRows 2 (Fin u) (Fin v)) K[X]) (p : K[X]),
        DegreeBound E 1 → E*G = (-p) •
          (fun i z => if Sum.inr i=z then 1 else 0 : Matrix (Fin v) (Fin u ⊕ Fin v) K[X]) →
        E=0 ∧ p=0 := by
  let A := separatedMonomialColumns (K := K) (Fin (u-1)) 4
  let D := threeSeparatedColumns (K := K) (Fin (v-2))
  let W := Matrix.fromBlocks A 0 0 D
  let T := Matrix.fromBlocks (familySLWitness (K := K)) 0 0 W
  have hA0 : Function.Injective (A.map (Polynomial.evalRingHom 0)).mulVec := by
    intro x y hxy
    funext z
    have hrow (j : Fin (u-1)) : Polynomial.eval 0 (A (Sum.inl z) j) = if z=j then 1 else 0 := by
      dsimp [A,separatedMonomialColumns]
      split_ifs <;> simp
    simpa only [Matrix.mulVec,dotProduct,Matrix.map_apply,Polynomial.coe_evalRingHom,
      hrow,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,if_true] using
      congrFun hxy (Sum.inl z)
  have hWmap : W.map (Polynomial.evalRingHom 0) =
      Matrix.fromBlocks (A.map (Polynomial.evalRingHom 0)) 0 0 (D.map (Polynomial.evalRingHom 0)) := by
    funext x z
    cases x <;> cases z <;> simp [W,Matrix.fromBlocks]
  have hW0 : Function.Injective (W.map (Polynomial.evalRingHom 0)).mulVec := by
    rw [hWmap]
    exact field_block_sum_injective _ _ hA0 threeSeparatedColumns_eval_zero_injective
  have hTmap : T.map (Polynomial.evalRingHom 0) =
      Matrix.fromBlocks ((familySLWitness (K := K)).map (Polynomial.evalRingHom 0)) 0 0
        (W.map (Polynomial.evalRingHom 0)) := by
    funext x z
    cases x <;> cases z <;> simp [T,Matrix.fromBlocks]
  have hT0 : Function.Injective (T.map (Polynomial.evalRingHom 0)).mulVec := by
    rw [hTmap]
    exact field_block_sum_injective _ _ familySLWitness_eval_zero_injective hW0
  have hWd : DegreeBound W 4 := block_sum_degree A D 4
    (separatedMonomialColumns_degree 4) threeSeparatedColumns_degree
  have hTc (x) (z : Fin 3) : (T x (Sum.inl z)).natDegree ≤ ![5,5,4] z := by
    cases x
    · exact familySLWitness_column_degree _ z
    · simp [T,Matrix.fromBlocks]
  have hTr (x) (z) : (T x (Sum.inr z)).natDegree ≤ 4 := by
    cases x
    · simp [T,Matrix.fromBlocks]
    · exact hWd _ z
  have hzero : ∀ (E : Matrix (Fin 2 ⊕ Fin (v-2))
      (Fin 8 ⊕ ((Fin (u-1) ⊕ Fin (u-1)) ⊕ (Fin 3 × Fin (v-2)))) K[X]) (p : K[X]),
      DegreeBound E 1 → E*T = (-p) •
        (fun i z => if Sum.map Fin.castSucc Sum.inr i=z then 1 else 0 :
          Matrix (Fin 2 ⊕ Fin (v-2)) (Fin 3 ⊕ (Fin (u-1) ⊕ Fin (v-2))) K[X]) → E=0 ∧ p=0 := by
    intro E p hE hrel
    apply block_sum_partial_scalar_obstruction familySLWitness W Fin.castSucc Sum.inr 1
      (0 : Fin 2) familySLWitness_partial_scalar_obstruction _ E p hE hrel
    exact block_sum_row_zero A D 1 (separatedMonomialColumns_row_zero 1 4 (by decide))
      threeSeparatedColumns_affine_row_zero
  let eL : Fin u ≃ Fin 1 ⊕ Fin (u-1) := Fintype.equivOfCardEq (by simp; omega)
  let eH : Fin v ≃ Fin 2 ⊕ Fin (v-2) := Fintype.equivOfCardEq (by simp; omega)
  let ep : (Fin 1 ⊕ Fin (u-1)) ⊕ (Fin 2 ⊕ Fin (v-2)) ≃
      (Fin 2 ⊕ Fin 1) ⊕ (Fin (u-1) ⊕ Fin (v-2)) :=
    (Equiv.sumSumSumComm _ _ _ _).trans
      (Equiv.sumCongr (Equiv.sumComm _ _) (Equiv.refl _))
  let ec : (Fin u ⊕ Fin v) ≃ Fin 3 ⊕ (Fin (u-1) ⊕ Fin (v-2)) :=
    ((Equiv.sumCongr eL eH).trans ep).trans (Equiv.sumCongr finSumFinEquiv (Equiv.refl _))
  let er : MixedScalarRows 2 (Fin u) (Fin v) ≃
      Fin 8 ⊕ ((Fin (u-1) ⊕ Fin (u-1)) ⊕ (Fin 3 × Fin (v-2))) :=
    Fintype.equivOfCardEq (by simp [MixedScalarRows]; omega)
  have hec (i : Fin 2 ⊕ Fin (v-2)) : ec (Sum.inr (eH.symm i)) = Sum.map Fin.castSucc Sum.inr i := by
    cases i with
    | inl i => fin_cases i <;> simp [ec,ep,Equiv.sumSumSumComm,finSumFinEquiv]
    | inr i => simp [ec,ep,Equiv.sumSumSumComm]
  let G := T.submatrix er ec
  have hG0 : Function.Injective (G.map (Polynomial.evalRingHom 0)).mulVec := by
    intro x y hxy
    have hh : (fun z => x (ec.symm z)) = (fun z => y (ec.symm z)) := by
      apply hT0
      funext i
      have h := congrFun hxy (er.symm i)
      change ((T.map (Polynomial.evalRingHom 0)).submatrix er ec *ᵥ x) (er.symm i) =
        ((T.map (Polynomial.evalRingHom 0)).submatrix er ec *ᵥ y) (er.symm i) at h
      simpa only [Matrix.submatrix_mulVec_equiv,Function.comp_apply,Equiv.apply_symm_apply] using h
    funext z
    simpa only [Equiv.symm_apply_apply] using congrFun hh (ec z)
  refine ⟨G,?_,polynomial_matrix_injective_of_zero G hG0,hG0,?_⟩
  · intro x z
    cases z with
    | inl z =>
      cases hz : eL z with
      | inl z' =>
        fin_cases z'
        simpa [G,ec,ep,Equiv.sumSumSumComm,finSumFinEquiv,hz,mixedColumnShift] using hTc (er x) 2
      | inr z' =>
        simpa [G,ec,ep,Equiv.sumSumSumComm,hz,mixedColumnShift] using hTr (er x) (Sum.inl z')
    | inr z =>
      cases hz : eH z with
      | inl z' =>
        have h := hTc (er x) z'.castSucc
        fin_cases z' <;>
          simpa [G,ec,ep,Equiv.sumSumSumComm,finSumFinEquiv,hz,mixedColumnShift] using h
      | inr z' =>
        have h := (hTr (er x) (Sum.inr z')).trans (by decide : 4 ≤ 5)
        simpa [G,ec,ep,Equiv.sumSumSumComm,hz,mixedColumnShift] using h
  · intro E p hE hrel
    let E' := E.submatrix eH.symm er.symm
    have hE' : DegreeBound E' 1 := fun i z => hE (eH.symm i) (er.symm z)
    have hrel' : E'*T = (-p) •
        (fun i z => if Sum.map Fin.castSucc Sum.inr i=z then 1 else 0 :
          Matrix (Fin 2 ⊕ Fin (v-2)) (Fin 3 ⊕ (Fin (u-1) ⊕ Fin (v-2))) K[X]) := by
      have hEE : E'.submatrix eH er=E := by funext i z; simp [E']
      change E*T.submatrix er ec = _ at hrel
      rw [← hEE,Matrix.submatrix_mul_equiv] at hrel
      funext i z
      have h := congrFun (congrFun hrel (eH.symm i)) (ec.symm z)
      have he : (Sum.inr (eH.symm i)=ec.symm z) ↔ Sum.map Fin.castSucc Sum.inr i=z := by
        rw [Equiv.eq_symm_apply,hec]
      simpa only [Matrix.submatrix_apply,Equiv.apply_symm_apply,Matrix.smul_apply,
        Pi.smul_apply,smul_eq_mul,he] using h
    obtain ⟨hE0,hp0⟩ := hzero E' p hE' hrel'
    refine ⟨?_,hp0⟩
    funext i z
    have h := congrFun (congrFun hE0 (eH i)) (er z)
    simpa [E'] using h

end FD56
