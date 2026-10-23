/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MixedScalarWitness

/-! A missing coefficient realizes the scalar constraints for adjacent degrees three and four. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K L H : Type*} [Field K] [Fintype L] [Fintype H]
  [DecidableEq L] [DecidableEq H] {s : ℕ}

def mixedThreeScalarBlock (hs : s ≤ 8) (k : Fin s) : Fin 4 :=
  ⟨k.val / 2, by have := k.isLt; omega⟩

def mixedThreeScalarWitness (hs : s ≤ 8) (f : Fin s ↪ H × L) :
    Matrix (MixedScalarRows 3 L H) (L ⊕ H) K[X]
  | Sum.inl x, Sum.inl j => if x.2 = j then X^(if x.1 = 2 then 5 else 2*x.1.val) else 0
  | Sum.inl _, Sum.inr _ => 0
  | Sum.inr x, Sum.inr j => if x.2 = j then X^(2*x.1.val) else 0
  | Sum.inr x, Sum.inl j => ∑ k : Fin s,
      if x.1 = mixedThreeScalarBlock hs k ∧ x.2 = (f k).1 ∧ j = (f k).2
      then X^(4-k.val%2) else 0

omit [Fintype L] [Fintype H] in
theorem mixedThreeScalarWitness_degree (hs : s ≤ 8) (f : Fin s ↪ H × L)
    (x : MixedScalarRows 3 L H) (j : L ⊕ H) :
    (mixedThreeScalarWitness (K := K) hs f x j).natDegree ≤ 5 + mixedColumnShift j := by
  cases x with
  | inl x =>
    cases j with
    | inl j =>
      simp only [mixedThreeScalarWitness,mixedColumnShift,Sum.elim_inl,add_zero]
      split_ifs
      · simp
      · exact (natDegree_X_pow_le _).trans (by have := x.1.isLt; omega)
      · simp
    | inr j => simp [mixedThreeScalarWitness]
  | inr x =>
    cases j with
    | inl j =>
      apply natDegree_sum_le_of_forall_le
      intro k _
      split_ifs
      · exact (natDegree_X_pow_le _).trans (by simp [mixedColumnShift]; omega)
      · simp
    | inr j =>
      simp only [mixedThreeScalarWitness,mixedColumnShift,Sum.elim_inr]
      split_ifs
      · exact (natDegree_X_pow_le _).trans (by have := x.1.isLt; omega)
      · simp

theorem mixedThreeScalarWitness_eval_zero_injective (hs : s ≤ 8) (f : Fin s ↪ H × L) :
    Function.Injective
      ((mixedThreeScalarWitness (K := K) hs f).map (Polynomial.evalRingHom 0)).mulVec := by
  intro u v huv
  funext i
  cases i with
  | inl i =>
    have h := congrFun huv (Sum.inl ((0 : Fin 3),i))
    have hrow (j : L ⊕ H) :
        Polynomial.eval 0 (mixedThreeScalarWitness (K := K) hs f (Sum.inl (0,i)) j) =
          if Sum.inl i = j then 1 else 0 := by
      cases j <;> simp [mixedThreeScalarWitness]
      split_ifs <;> simp
    simpa only [Matrix.mulVec,dotProduct,Matrix.map_apply,Polynomial.coe_evalRingHom,
      hrow,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,if_true] using h
  | inr i =>
    have h := congrFun huv (Sum.inr ((0 : Fin 4),i))
    have hrow (j : L ⊕ H) :
        Polynomial.eval 0 (mixedThreeScalarWitness (K := K) hs f (Sum.inr (0,i)) j) =
          if Sum.inr i = j then 1 else 0 := by
      cases j with
      | inl j =>
        simp only [mixedThreeScalarWitness,Polynomial.eval_finset_sum,Sum.inr_ne_inl,if_false]
        apply Finset.sum_eq_zero
        intro k _
        have hn : 4-k.val%2 ≠ 0 := by have := Nat.mod_lt k.val (by omega : 0<2); omega
        split_ifs <;> simp [hn]
      | inr j =>
        simp only [mixedThreeScalarWitness,Fin.val_zero,mul_zero,pow_zero,Sum.inr.injEq]
        split_ifs <;> simp
    simpa only [Matrix.mulVec,dotProduct,Matrix.map_apply,Polynomial.coe_evalRingHom,
      hrow,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,if_true] using h

theorem mixedThreeScalarWitness_injective (hs : s ≤ 8) (f : Fin s ↪ H × L) :
    Function.Injective (mixedThreeScalarWitness (K := K) hs f).mulVec := by
  apply polynomial_matrix_injective_of_zero
  exact mixedThreeScalarWitness_eval_zero_injective hs f

theorem mixedThreeScalarWitness_mul_right (hs : s ≤ 8) (f : Fin s ↪ H × L)
    (E : Matrix H (MixedScalarRows 3 L H) K[X]) (i j : H) :
    (E * mixedThreeScalarWitness (K := K) hs f) i (Sum.inr j) =
      E i (Sum.inr (0,j)) + E i (Sum.inr (1,j))*X^2 +
      E i (Sum.inr (2,j))*X^4 + E i (Sum.inr (3,j))*X^6 := by
  simp [mixedThreeScalarWitness,Matrix.mul_apply,Fintype.sum_sum_type,Fintype.sum_prod_type,
    Fin.sum_univ_succ,mul_ite,add_assoc]

theorem mixedThreeScalarWitness_mul_left (hs : s ≤ 8) (f : Fin s ↪ H × L)
    (E : Matrix H (MixedScalarRows 3 L H) K[X]) (i : H) (j : L) :
    (E * mixedThreeScalarWitness (K := K) hs f) i (Sum.inl j) =
      E i (Sum.inl (0,j)) + E i (Sum.inl (1,j))*X^2 + E i (Sum.inl (2,j))*X^5 +
      ∑ k : Fin s, if j = (f k).2 then
        E i (Sum.inr (mixedThreeScalarBlock hs k,(f k).1))*X^(4-k.val%2) else 0 := by
  simp only [Matrix.mul_apply,Fintype.sum_sum_type,mixedThreeScalarWitness]
  congr 1
  · simp [Fintype.sum_prod_type,Fin.sum_univ_succ,mul_ite,add_assoc]
  · simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hj : j = (f k).2
    · simp [Fintype.sum_prod_type,hj,mul_ite,ite_and]
    · simp [hj]

private theorem coeff_ite (p : Prop) [Decidable p] (f g : K[X]) (d : ℕ) :
    (if p then f else g).coeff d = if p then f.coeff d else g.coeff d := by
  split_ifs <;> rfl

theorem mixedThreeScalarWitness_scalar_obstruction (b : H) (hs : s ≤ 8)
    (f : Fin s ↪ H × L) (E : Matrix H (MixedScalarRows 3 L H) K[X]) (c : K[X])
    (hE : DegreeBound E 1)
    (hrel : E * mixedThreeScalarWitness (K := K) hs f =
      (-c) • (fun i j => if Sum.inr i = j then 1 else 0 : Matrix H (L ⊕ H) K[X]))
    (htail : ∀ k : Fin 8, s ≤ k.val → c.coeff k.val = 0) : E = 0 ∧ c = 0 := by
  have hcE (i : H) (x : MixedScalarRows 3 L H) (k : ℕ) (hk : 1 < k) :
      (E i x).coeff k = 0 := coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hE i x) hk)
  have hcoeff (d : ℕ) (i : H) (j : L ⊕ H) :
      ((E * mixedThreeScalarWitness (K := K) hs f) i j).coeff d =
        if Sum.inr i = j then -(c.coeff d) else 0 := by
    have h := congrArg (fun A : Matrix H (L ⊕ H) K[X] => (A i j).coeff d) hrel
    simpa [Matrix.smul_apply,mul_ite,coeff_ite] using h
  have hhigh (l : Fin 4) (q : Fin 2) (i j : H) :
      (E i (Sum.inr (l,j))).coeff q.val =
        if i = j then -(c.coeff (2*l.val+q.val)) else 0 := by
    have h := hcoeff (2*l.val+q.val) i (Sum.inr j)
    fin_cases l <;> fin_cases q <;>
      simpa [mixedThreeScalarWitness_mul_right,coeff_add,coeff_mul_X_pow',hcE] using h
  have hgap (i : H) (j : L) :
      (∑ k : Fin s, if i = (f k).1 ∧ j = (f k).2 then -(c.coeff k.val) else 0) = 0 := by
    have h := hcoeff 4 i (Sum.inl j)
    simp only [mixedThreeScalarWitness_mul_left,coeff_add,coeff_mul_X_pow',
      finset_sum_coeff,coeff_ite,coeff_zero,Sum.inr_ne_inl,if_false] at h
    norm_num [hcE] at h
    convert h using 1
    apply Finset.sum_congr rfl
    intro k _
    have hmod : k.val%2 < 2 := Nat.mod_lt _ (by omega)
    have hsub : 4 - (4-k.val%2) = k.val%2 := by omega
    have hsuble : 4-k.val%2 ≤ 4 := by omega
    have he : 2*(mixedThreeScalarBlock hs k).val + k.val%2 = k.val := by
      dsimp [mixedThreeScalarBlock]
      omega
    have hh := hhigh (mixedThreeScalarBlock hs k) ⟨k.val%2,hmod⟩ i (f k).1
    simp only [Fin.val_mk,he] at hh
    simp only [hsuble,if_true,hsub,hh]
    split_ifs <;> simp_all
  have hlow (k : Fin s) : c.coeff k.val = 0 := by
    have h := hgap (f k).1 (f k).2
    have he (l : Fin s) : ((f k).1 = (f l).1 ∧ (f k).2 = (f l).2) ↔ l = k := by
      constructor
      · intro h
        exact (f.injective (Prod.ext h.1 h.2)).symm
      · rintro rfl
        exact ⟨rfl,rfl⟩
    simpa [he] using h
  have hc7 : c.natDegree ≤ 7 := by
    have hG : DegreeBound (mixedThreeScalarWitness (K := K) hs f) 6 := by
      intro x j
      exact (mixedThreeScalarWitness_degree hs f x j).trans (by cases j <;> simp [mixedColumnShift])
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
  have hright (i j : H) (l : Fin 4) : E i (Sum.inr (l,j)) = 0 := by
    rw [eq_X_add_C_of_natDegree_le_one (hE i (Sum.inr (l,j)))]
    have h0 := hhigh l 0 i j
    have h1 := hhigh l 1 i j
    simp only [hc,coeff_zero,neg_zero,ite_self] at h0 h1
    simp only [Fin.val_zero] at h0
    simp only [Fin.val_one] at h1
    simp [h0,h1]
  have hleft (i : H) (j : L) (l : Fin 3) (q : Fin 2) :
      (E i (Sum.inl (l,j))).coeff q.val = 0 := by
    have h := hcoeff ((if l=2 then 5 else 2*l.val)+q.val) i (Sum.inl j)
    fin_cases l <;> fin_cases q <;>
      simpa [mixedThreeScalarWitness_mul_left,hright,coeff_add,coeff_mul_X_pow',hcE] using h
  refine ⟨?_,hc⟩
  funext i x
  cases x with
  | inr x => exact hright i x.2 x.1
  | inl x =>
    rw [eq_X_add_C_of_natDegree_le_one (hE i (Sum.inl x))]
    have h0 := hleft i x.2 x.1 0
    have h1 := hleft i x.2 x.1 1
    simp only [Fin.val_zero] at h0
    simp only [Fin.val_one] at h1
    simp [h0,h1]

theorem exists_mixed_three_scalar_witness (u v : ℕ) (hv : 0 < v) :
    ∃ G : Matrix (MixedScalarRows 3 (Fin u) (Fin v)) (Fin u ⊕ Fin v) K[X],
      (∀ x j, (G x j).natDegree ≤ 5 + mixedColumnShift j) ∧
      Function.Injective G.mulVec ∧
      Function.Injective (G.map (Polynomial.evalRingHom 0)).mulVec ∧
      ∀ (E : Matrix (Fin v) (MixedScalarRows 3 (Fin u) (Fin v)) K[X]) (c : K[X]),
        DegreeBound E 1 → E * G = (-c) •
          (fun i j => if Sum.inr i = j then 1 else 0 : Matrix (Fin v) (Fin u ⊕ Fin v) K[X]) →
        (∀ k : Fin (8-u*v), c.coeff (u*v+k.val) = 0) → E = 0 ∧ c = 0 := by
  let b : Fin v := ⟨0,hv⟩
  let s := min 8 (u*v)
  have hs : s ≤ 8 := min_le_left _ _
  have hcard : s ≤ Fintype.card (Fin v × Fin u) := by
    simp [s,Nat.mul_comm]
  let f : Fin s ↪ Fin v × Fin u :=
    { toFun := fun i => (Fintype.equivFin _).symm ⟨i.val, lt_of_lt_of_le i.isLt hcard⟩
      inj' := by
        intro i j hij
        have h := (Fintype.equivFin _).symm.injective hij
        exact Fin.ext (congrArg (fun x : Fin (Fintype.card (Fin v × Fin u)) => x.val) h) }
  refine ⟨mixedThreeScalarWitness hs f, mixedThreeScalarWitness_degree hs f,
    mixedThreeScalarWitness_injective hs f, mixedThreeScalarWitness_eval_zero_injective hs f, ?_⟩
  intro E c hE hrel htail
  apply mixedThreeScalarWitness_scalar_obstruction b hs f E c hE hrel
  intro k hk
  have hN : u*v ≤ k.val := by have := k.isLt; dsimp [s] at hk; omega
  let l : Fin (8-u*v) := ⟨k.val-u*v,by have := k.isLt; omega⟩
  have hl : u*v+l.val=k.val := by dsimp [l]; omega
  simpa only [← hl] using htail l

end FD56
