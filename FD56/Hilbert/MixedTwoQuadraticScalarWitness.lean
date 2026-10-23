/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MixedScalarWitness

/-! Calibration columns remove overlap parameters before the scalar coefficients are selected. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K H J : Type*} [Field K] [Fintype H] [Fintype J]
  [DecidableEq H] [DecidableEq J] {s : ℕ}

def mixedTwoQuadraticBlock (k : Fin 8) : Fin 3 := ⟨k.val/3,by have := k.isLt; omega⟩
def mixedTwoQuadraticCoeff (k : Fin 8) : ℕ := if k.val<6 then k.val%3 else k.val-5

theorem mixedTwoQuadraticCoeff_lt (k : Fin 8) : mixedTwoQuadraticCoeff k < 3 := by
  fin_cases k <;> decide

def mixedTwoQuadraticScalarWitness (hs : s ≤ 8) (f : Fin s ↪ H × J) :
    Matrix (MixedScalarRows 2 (H ⊕ J) H) ((H ⊕ J) ⊕ H) K[X]
  | Sum.inl x, Sum.inl j => if x.2 = j then X^(4*x.1.val) else 0
  | Sum.inl _, Sum.inr _ => 0
  | Sum.inr x, Sum.inr j => if x.2 = j then X^(if x.1=2 then 5 else 3*x.1.val) else 0
  | Sum.inr x, Sum.inl (Sum.inl j) => if x.1=2 ∧ x.2=j then X^3 else 0
  | Sum.inr x, Sum.inl (Sum.inr j) => ∑ k : Fin s,
      if x.1 = mixedTwoQuadraticBlock (Fin.castLE hs k) ∧ x.2=(f k).1 ∧ j=(f k).2
      then X^(3-mixedTwoQuadraticCoeff (Fin.castLE hs k)) else 0

omit [Fintype H] [Fintype J] in
theorem mixedTwoQuadraticScalarWitness_degree (hs : s ≤ 8) (f : Fin s ↪ H × J)
    (x : MixedScalarRows 2 (H ⊕ J) H) (j : (H ⊕ J) ⊕ H) :
    (mixedTwoQuadraticScalarWitness (K := K) hs f x j).natDegree ≤ 4+mixedColumnShift j := by
  cases x with
  | inl x =>
    cases j with
    | inl j =>
      simp only [mixedTwoQuadraticScalarWitness,mixedColumnShift,Sum.elim_inl,add_zero]
      split_ifs
      · exact (natDegree_X_pow_le _).trans (by have := x.1.isLt; omega)
      · simp
    | inr j => simp [mixedTwoQuadraticScalarWitness]
  | inr x =>
    cases j with
    | inr j =>
      simp only [mixedTwoQuadraticScalarWitness,mixedColumnShift,Sum.elim_inr]
      split_ifs with hij hl
      · simp
      · have hn : x.1.val ≠ 2 := by intro he; exact hl (Fin.ext he)
        exact (natDegree_X_pow_le _).trans (by have := x.1.isLt; omega)
      · simp
    | inl j =>
      cases j with
      | inl j => simp only [mixedTwoQuadraticScalarWitness]; split_ifs <;> simp [mixedColumnShift]
      | inr j =>
        apply natDegree_sum_le_of_forall_le
        intro k _
        split_ifs
        · exact (natDegree_X_pow_le _).trans (by simp [mixedColumnShift]; omega)
        · simp

theorem mixedTwoQuadraticScalarWitness_eval_zero_injective (hs : s ≤ 8) (f : Fin s ↪ H × J) :
    Function.Injective
      ((mixedTwoQuadraticScalarWitness (K := K) hs f).map (Polynomial.evalRingHom 0)).mulVec := by
  intro u v huv
  funext i
  cases i with
  | inl i =>
    have h := congrFun huv (Sum.inl ((0 : Fin 2),i))
    have hrow (j : (H ⊕ J) ⊕ H) :
        Polynomial.eval 0 (mixedTwoQuadraticScalarWitness (K := K) hs f (Sum.inl (0,i)) j) =
          if Sum.inl i = j then 1 else 0 := by
      cases j <;> simp only [mixedTwoQuadraticScalarWitness,Fin.val_zero,mul_zero,pow_zero,
        Sum.inl.injEq,Sum.inl_ne_inr,if_false]
      · split_ifs <;> simp
      · simp
    simpa only [Matrix.mulVec,dotProduct,Matrix.map_apply,Polynomial.coe_evalRingHom,
      hrow,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,if_true] using h
  | inr i =>
    have h := congrFun huv (Sum.inr ((0 : Fin 3),i))
    have hrow (j : (H ⊕ J) ⊕ H) :
        Polynomial.eval 0 (mixedTwoQuadraticScalarWitness (K := K) hs f (Sum.inr (0,i)) j) =
          if Sum.inr i = j then 1 else 0 := by
      have hn : (0 : Fin 3) ≠ 2 := by decide
      cases j with
      | inr j =>
        simp only [mixedTwoQuadraticScalarWitness,hn,if_false,Fin.val_zero,mul_zero,pow_zero,Sum.inr.injEq]
        split_ifs <;> simp
      | inl j =>
        cases j with
        | inl j => simp [mixedTwoQuadraticScalarWitness,hn]
        | inr j =>
          simp only [mixedTwoQuadraticScalarWitness,Polynomial.eval_finset_sum,Sum.inr_ne_inl,if_false]
          apply Finset.sum_eq_zero
          intro k _
          have hn : 3-mixedTwoQuadraticCoeff (Fin.castLE hs k) ≠ 0 := by
            have := mixedTwoQuadraticCoeff_lt (Fin.castLE hs k); omega
          split_ifs <;> simp [hn]
    simpa only [Matrix.mulVec,dotProduct,Matrix.map_apply,Polynomial.coe_evalRingHom,
      hrow,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,if_true] using h

theorem mixedTwoQuadraticScalarWitness_injective (hs : s ≤ 8) (f : Fin s ↪ H × J) :
    Function.Injective (mixedTwoQuadraticScalarWitness (K := K) hs f).mulVec := by
  apply polynomial_matrix_injective_of_zero
  exact mixedTwoQuadraticScalarWitness_eval_zero_injective hs f

theorem mixedTwoQuadraticScalarWitness_mul_right (hs : s ≤ 8) (f : Fin s ↪ H × J)
    (E : Matrix H (MixedScalarRows 2 (H ⊕ J) H) K[X]) (i j : H) :
    (E * mixedTwoQuadraticScalarWitness (K := K) hs f) i (Sum.inr j) =
      E i (Sum.inr (0,j)) + E i (Sum.inr (1,j))*X^3 + E i (Sum.inr (2,j))*X^5 := by
  simp [mixedTwoQuadraticScalarWitness,Matrix.mul_apply,Fintype.sum_sum_type,Fintype.sum_prod_type,
    Fin.sum_univ_succ,mul_ite,add_assoc]

theorem mixedTwoQuadraticScalarWitness_mul_calibration (hs : s ≤ 8) (f : Fin s ↪ H × J)
    (E : Matrix H (MixedScalarRows 2 (H ⊕ J) H) K[X]) (i j : H) :
    (E * mixedTwoQuadraticScalarWitness (K := K) hs f) i (Sum.inl (Sum.inl j)) =
      E i (Sum.inl (0,Sum.inl j)) + E i (Sum.inl (1,Sum.inl j))*X^4 +
      E i (Sum.inr (2,j))*X^3 := by
  simp [mixedTwoQuadraticScalarWitness,Matrix.mul_apply,Fintype.sum_sum_type,Fintype.sum_prod_type,
    Fin.sum_univ_succ,mul_ite,ite_and,add_assoc]

theorem mixedTwoQuadraticScalarWitness_mul_free (hs : s ≤ 8) (f : Fin s ↪ H × J)
    (E : Matrix H (MixedScalarRows 2 (H ⊕ J) H) K[X]) (i : H) (j : J) :
    (E * mixedTwoQuadraticScalarWitness (K := K) hs f) i (Sum.inl (Sum.inr j)) =
      E i (Sum.inl (0,Sum.inr j)) + E i (Sum.inl (1,Sum.inr j))*X^4 +
      ∑ k : Fin s, if j=(f k).2 then
        E i (Sum.inr (mixedTwoQuadraticBlock (Fin.castLE hs k),(f k).1)) *
          X^(3-mixedTwoQuadraticCoeff (Fin.castLE hs k)) else 0 := by
  simp only [Matrix.mul_apply,Fintype.sum_sum_type,mixedTwoQuadraticScalarWitness]
  congr 1
  · simp [Fintype.sum_prod_type,Fin.sum_univ_succ,mul_ite,add_assoc]
  · simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hj : j=(f k).2
    · simp [Fintype.sum_prod_type,hj,mul_ite,ite_and]
    · simp [hj]

private theorem coeff_ite (p : Prop) [Decidable p] (f g : K[X]) (d : ℕ) :
    (if p then f else g).coeff d = if p then f.coeff d else g.coeff d := by
  split_ifs <;> rfl

private theorem polynomial_quadratic_zero (p : K[X]) (hp : p.natDegree ≤ 2)
    (hc : ∀ q : Fin 3, p.coeff q.val = 0) : p = 0 := by
  ext k
  by_cases hk : k < 3
  · exact hc ⟨k,hk⟩
  · exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp (by omega))

theorem mixedTwoQuadraticScalarWitness_scalar_obstruction (b : H) (hs : s ≤ 8)
    (f : Fin s ↪ H × J) (E : Matrix H (MixedScalarRows 2 (H ⊕ J) H) K[X]) (c : K[X])
    (hE : DegreeBound E 2)
    (hrel : E * mixedTwoQuadraticScalarWitness (K := K) hs f =
      (-c) • (fun i j => if Sum.inr i = j then 1 else 0 : Matrix H ((H ⊕ J) ⊕ H) K[X]))
    (htail : ∀ k : Fin 8, s ≤ k.val → c.coeff k.val = 0) : E = 0 ∧ c = 0 := by
  have hcE (i : H) (x : MixedScalarRows 2 (H ⊕ J) H) (k : ℕ) (hk : 2 < k) :
      (E i x).coeff k = 0 := coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hE i x) hk)
  have hcoeff (d : ℕ) (i : H) (j : (H ⊕ J) ⊕ H) :
      ((E * mixedTwoQuadraticScalarWitness (K := K) hs f) i j).coeff d =
        if Sum.inr i = j then -(c.coeff d) else 0 := by
    have h := congrArg (fun A : Matrix H ((H ⊕ J) ⊕ H) K[X] => (A i j).coeff d) hrel
    simpa [Matrix.smul_apply,mul_ite,coeff_ite] using h
  have hT (i j : H) : (E i (Sum.inr (2,j))).coeff 0 = 0 := by
    have h := hcoeff 3 i (Sum.inl (Sum.inl j))
    simpa [mixedTwoQuadraticScalarWitness_mul_calibration,coeff_add,coeff_mul_X_pow',hcE] using h
  have hselect (k : Fin 8) (i j : H) :
      (E i (Sum.inr (mixedTwoQuadraticBlock k,j))).coeff (mixedTwoQuadraticCoeff k) =
        if i=j then -(c.coeff k.val) else 0 := by
    have h := hcoeff k.val i (Sum.inr j)
    fin_cases k <;>
      simpa [mixedTwoQuadraticBlock,mixedTwoQuadraticCoeff,mixedTwoQuadraticScalarWitness_mul_right,
        coeff_add,coeff_mul_X_pow',hcE,hT] using h
  have hgap (i : H) (j : J) :
      (∑ k : Fin s, if i=(f k).1 ∧ j=(f k).2 then -(c.coeff k.val) else 0) = 0 := by
    have h := hcoeff 3 i (Sum.inl (Sum.inr j))
    simp only [mixedTwoQuadraticScalarWitness_mul_free,coeff_add,coeff_mul_X_pow',
      finset_sum_coeff,coeff_ite,coeff_zero,Sum.inr_ne_inl,if_false] at h
    norm_num [hcE] at h
    convert h using 1
    apply Finset.sum_congr rfl
    intro k _
    have hq := mixedTwoQuadraticCoeff_lt (Fin.castLE hs k)
    have hsub : 3-(3-mixedTwoQuadraticCoeff (Fin.castLE hs k)) =
        mixedTwoQuadraticCoeff (Fin.castLE hs k) := by omega
    have hle : 3-mixedTwoQuadraticCoeff (Fin.castLE hs k) ≤ 3 := by omega
    simp only [hle,if_true,hsub,hselect,Fin.coe_castLE]
    split_ifs <;> simp_all
  have hlow (k : Fin s) : c.coeff k.val = 0 := by
    have h := hgap (f k).1 (f k).2
    have he (l : Fin s) : ((f k).1=(f l).1 ∧ (f k).2=(f l).2) ↔ l=k := by
      constructor
      · intro h
        exact (f.injective (Prod.ext h.1 h.2)).symm
      · rintro rfl
        exact ⟨rfl,rfl⟩
    simpa [he] using h
  have hc7 : c.natDegree ≤ 7 := by
    have hG : DegreeBound (mixedTwoQuadraticScalarWitness (K := K) hs f) 5 := by
      intro x j
      exact (mixedTwoQuadraticScalarWitness_degree hs f x j).trans (by cases j <;> simp [mixedColumnShift])
    have hh := degreeBound_mul hE hG b (Sum.inr b)
    rw [hrel] at hh
    simpa using hh
  have hc : c = 0 := by
    ext k
    by_cases hk : k < 8
    · by_cases hks : k < s
      · exact hlow ⟨k,hks⟩
      · exact htail ⟨k,hk⟩ (Nat.le_of_not_gt hks)
    · exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hc7 (by omega))
  have hright (i j : H) (l : Fin 3) : E i (Sum.inr (l,j)) = 0 := by
    apply polynomial_quadratic_zero _ (hE i (Sum.inr (l,j)))
    intro q
    fin_cases l <;> fin_cases q
    · simpa [mixedTwoQuadraticBlock,mixedTwoQuadraticCoeff,hc] using hselect 0 i j
    · simpa [mixedTwoQuadraticBlock,mixedTwoQuadraticCoeff,hc] using hselect 1 i j
    · simpa [mixedTwoQuadraticBlock,mixedTwoQuadraticCoeff,hc] using hselect 2 i j
    · simpa [mixedTwoQuadraticBlock,mixedTwoQuadraticCoeff,hc] using hselect 3 i j
    · simpa [mixedTwoQuadraticBlock,mixedTwoQuadraticCoeff,hc] using hselect 4 i j
    · simpa [mixedTwoQuadraticBlock,mixedTwoQuadraticCoeff,hc] using hselect 5 i j
    · exact hT i j
    · simpa [mixedTwoQuadraticBlock,mixedTwoQuadraticCoeff,hc] using hselect 6 i j
    · simpa [mixedTwoQuadraticBlock,mixedTwoQuadraticCoeff,hc] using hselect 7 i j
  have hleft (i : H) (j : H ⊕ J) (l : Fin 2) : E i (Sum.inl (l,j)) = 0 := by
    apply polynomial_quadratic_zero _ (hE i (Sum.inl (l,j)))
    intro q
    have h := hcoeff (4*l.val+q.val) i (Sum.inl j)
    cases j <;> fin_cases l <;> fin_cases q <;>
      simpa [mixedTwoQuadraticScalarWitness_mul_calibration,mixedTwoQuadraticScalarWitness_mul_free,
        hright,coeff_add,coeff_mul_X_pow',hcE] using h
  refine ⟨?_,hc⟩
  funext i x
  cases x with
  | inl x => exact hleft i x.2 x.1
  | inr x => exact hright i x.2 x.1

theorem exists_mixed_two_quadratic_split_witness (v w : ℕ) (hv : 0 < v) :
    ∃ G : Matrix (MixedScalarRows 2 (Fin v ⊕ Fin w) (Fin v))
        ((Fin v ⊕ Fin w) ⊕ Fin v) K[X],
      (∀ x j, (G x j).natDegree ≤ 4+mixedColumnShift j) ∧
      Function.Injective G.mulVec ∧
      Function.Injective (G.map (Polynomial.evalRingHom 0)).mulVec ∧
      ∀ (E : Matrix (Fin v) (MixedScalarRows 2 (Fin v ⊕ Fin w) (Fin v)) K[X]) (c : K[X]),
        DegreeBound E 2 → E * G = (-c) •
          (fun i j => if Sum.inr i = j then 1 else 0 :
            Matrix (Fin v) ((Fin v ⊕ Fin w) ⊕ Fin v) K[X]) →
        (∀ k : Fin (8-v*w), c.coeff (v*w+k.val) = 0) → E = 0 ∧ c = 0 := by
  let b : Fin v := ⟨0,hv⟩
  let s := min 8 (v*w)
  have hs : s ≤ 8 := min_le_left _ _
  have hcard : s ≤ Fintype.card (Fin v × Fin w) := by simp [s]
  let f : Fin s ↪ Fin v × Fin w :=
    { toFun := fun i => (Fintype.equivFin _).symm ⟨i.val,lt_of_lt_of_le i.isLt hcard⟩
      inj' := by
        intro i j hij
        have h := (Fintype.equivFin _).symm.injective hij
        exact Fin.ext (congrArg (fun x : Fin (Fintype.card (Fin v × Fin w)) => x.val) h) }
  refine ⟨mixedTwoQuadraticScalarWitness hs f,mixedTwoQuadraticScalarWitness_degree hs f,
    mixedTwoQuadraticScalarWitness_injective hs f,mixedTwoQuadraticScalarWitness_eval_zero_injective hs f,?_⟩
  intro E c hE hrel htail
  apply mixedTwoQuadraticScalarWitness_scalar_obstruction b hs f E c hE hrel
  intro k hk
  have hN : v*w ≤ k.val := by have := k.isLt; dsimp [s] at hk; omega
  let l : Fin (8-v*w) := ⟨k.val-v*w,by have := k.isLt; omega⟩
  have hl : v*w+l.val=k.val := by dsimp [l]; omega
  simpa only [← hl] using htail l

theorem exists_mixed_two_quadratic_scalar_witness (u v : ℕ) (hv : 0 < v) (hvu : v ≤ u) :
    ∃ G : Matrix (MixedScalarRows 2 (Fin u) (Fin v)) (Fin u ⊕ Fin v) K[X],
      (∀ x j, (G x j).natDegree ≤ 4+mixedColumnShift j) ∧
      Function.Injective G.mulVec ∧
      Function.Injective (G.map (Polynomial.evalRingHom 0)).mulVec ∧
      ∀ (E : Matrix (Fin v) (MixedScalarRows 2 (Fin u) (Fin v)) K[X]) (c : K[X]),
        DegreeBound E 2 → E * G = (-c) •
          (fun i j => if Sum.inr i = j then 1 else 0 : Matrix (Fin v) (Fin u ⊕ Fin v) K[X]) →
        (∀ k : Fin (8-v*(u-v)), c.coeff (v*(u-v)+k.val) = 0) → E = 0 ∧ c = 0 := by
  obtain ⟨T,hT,_,hT0,hzero⟩ := exists_mixed_two_quadratic_split_witness (K := K) v (u-v) hv
  let e : Fin u ≃ Fin v ⊕ Fin (u-v) := Fintype.equivOfCardEq (by simp; omega)
  let ec : (Fin u ⊕ Fin v) ≃ ((Fin v ⊕ Fin (u-v)) ⊕ Fin v) := Equiv.sumCongr e (Equiv.refl _)
  let er : MixedScalarRows 2 (Fin u) (Fin v) ≃
      MixedScalarRows 2 (Fin v ⊕ Fin (u-v)) (Fin v) :=
    Equiv.sumCongr (Equiv.prodCongr (Equiv.refl _) e) (Equiv.refl _)
  let G := T.submatrix er ec
  have hG0 : Function.Injective (G.map (Polynomial.evalRingHom 0)).mulVec := by
    intro x y hxy
    have hh : (fun j => x (ec.symm j)) = (fun j => y (ec.symm j)) := by
      apply hT0
      funext i
      have h := congrFun hxy (er.symm i)
      change ((T.map (Polynomial.evalRingHom 0)).submatrix er ec *ᵥ x) (er.symm i) =
        ((T.map (Polynomial.evalRingHom 0)).submatrix er ec *ᵥ y) (er.symm i) at h
      simpa only [Matrix.submatrix_mulVec_equiv,Function.comp_apply,Equiv.apply_symm_apply] using h
    funext j
    simpa only [Equiv.symm_apply_apply] using congrFun hh (ec j)
  refine ⟨G,?_,polynomial_matrix_injective_of_zero G hG0,hG0,?_⟩
  · intro x j
    have h := hT (er x) (ec j)
    cases j <;> simpa [G,ec,mixedColumnShift] using h
  · intro E c hE hrel htail
    let E' := E.submatrix id er.symm
    have hE' : DegreeBound E' 2 := fun i j => hE i (er.symm j)
    have hrel' : E' * T = (-c) •
        (fun i j => if Sum.inr i = j then 1 else 0 :
          Matrix (Fin v) ((Fin v ⊕ Fin (u-v)) ⊕ Fin v) K[X]) := by
      have hEE : E'.submatrix id er = E := by funext i j; simp [E']
      change E * T.submatrix er ec = _ at hrel
      rw [← hEE,Matrix.submatrix_mul_equiv] at hrel
      funext i j
      have h := congrFun (congrFun hrel i) (ec.symm j)
      cases j <;> simpa [Matrix.submatrix_apply,Matrix.smul_apply,Equiv.eq_symm_apply,ec] using h
    obtain ⟨hE0,hc0⟩ := hzero E' c hE' hrel' htail
    refine ⟨?_,hc0⟩
    funext i j
    have h := congrFun (congrFun hE0 i) (er j)
    simpa [E'] using h

end FD56
