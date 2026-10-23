/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.UniformPartialWitness

/-! Scalar witnesses for two adjacent column degrees. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K L H : Type*} [Field K] [Fintype L] [Fintype H]
  [DecidableEq L] [DecidableEq H] {a s : ℕ}

abbrev MixedScalarRows (a : ℕ) (L H : Type*) := (Fin a × L) ⊕ (Fin (a+1) × H)
abbrev MixedScalarSlots (b : H) := Fin 3 × {p : H × (L ⊕ H) // p ≠ (b,Sum.inr b)}

def mixedColumnShift : L ⊕ H → ℕ := Sum.elim (fun _ => 0) (fun _ => 1)

def mixedScalarWitness (b : H) (f : Fin s ↪ MixedScalarSlots (L := L) b) :
    Matrix (MixedScalarRows a L H) (L ⊕ H) K[X]
  | Sum.inl x, j => if Sum.inl x.2 = j then X^x.1.val else 0
  | Sum.inr x, j => (if Sum.inr x.2 = j then X^x.1.val else 0) +
    (if h : x.1.val < s then
      if x.2 = (f ⟨x.1.val,h⟩).2.val.1 ∧ j = (f ⟨x.1.val,h⟩).2.val.2
      then X^(a + mixedColumnShift j + (f ⟨x.1.val,h⟩).1.val) else 0 else 0)

omit [Fintype L] [Fintype H] in
theorem mixedScalarWitness_degree (b : H) (f : Fin s ↪ MixedScalarSlots (L := L) b)
    (x : MixedScalarRows a L H) (j : L ⊕ H) :
    (mixedScalarWitness (K := K) b f x j).natDegree ≤ a + mixedColumnShift j + 2 := by
  cases x with
  | inl x =>
    simp only [mixedScalarWitness]
    split_ifs
    · exact (natDegree_X_pow_le _).trans (by have := x.1.isLt; omega)
    · simp
  | inr x =>
    apply natDegree_add_le_of_degree_le
    · split_ifs
      · exact (natDegree_X_pow_le _).trans (by have := x.1.isLt; omega)
      · simp
    · split_ifs with h
      · exact (natDegree_X_pow_le _).trans (by have := (f ⟨x.1.val,h⟩).1.isLt; omega)
      all_goals simp

private theorem coeff_ite (p : Prop) [Decidable p] (f g : K[X]) (d : ℕ) :
    (if p then f else g).coeff d = if p then f.coeff d else g.coeff d := by
  split_ifs <;> rfl

omit [Fintype L] [Fintype H] in
theorem mixedScalarWitness_coeff_low_left (b : H) (f : Fin s ↪ MixedScalarSlots (L := L) b)
    (l : Fin a) (j : L) (x : MixedScalarRows a L H) :
    (mixedScalarWitness (K := K) b f x (Sum.inl j)).coeff l.val =
      if x = Sum.inl (l,j) then 1 else 0 := by
  cases x with
  | inl x =>
    rcases x with ⟨k,i⟩
    have hlk : (l.val = k.val) ↔ k = l := by rw [Fin.val_inj]; exact eq_comm
    simp only [mixedScalarWitness, coeff_ite, coeff_X_pow, coeff_zero, Sum.inl.injEq,
      Prod.mk.injEq, hlk]
    split_ifs <;> simp_all
  | inr x =>
    simp only [mixedScalarWitness, Sum.inr_ne_inl, if_false, zero_add]
    split_ifs with h h'
    · have hn : l.val ≠ a + mixedColumnShift (Sum.inl j : L ⊕ H) + (f ⟨x.1.val,h⟩).1.val := by
        have := l.isLt; simp only [mixedColumnShift, Sum.elim_inl]; omega
      simp [coeff_X_pow, hn]
    all_goals simp

omit [Fintype L] [Fintype H] in
theorem mixedScalarWitness_coeff_low_right (b : H) (f : Fin s ↪ MixedScalarSlots (L := L) b)
    (l : Fin (a+1)) (j : H) (x : MixedScalarRows a L H) :
    (mixedScalarWitness (K := K) b f x (Sum.inr j)).coeff l.val =
      if x = Sum.inr (l,j) then 1 else 0 := by
  cases x with
  | inl x => simp [mixedScalarWitness]
  | inr x =>
    rcases x with ⟨k,i⟩
    have hlk : (l.val = k.val) ↔ k = l := by rw [Fin.val_inj]; exact eq_comm
    by_cases hk : k.val < s
    · have hn : l.val ≠ a + mixedColumnShift (Sum.inr j : L ⊕ H) + (f ⟨k.val,hk⟩).1.val := by
        have := l.isLt; simp only [mixedColumnShift, Sum.elim_inr]; omega
      simp only [mixedScalarWitness, dif_pos hk, coeff_add, coeff_ite, coeff_X_pow,
        coeff_zero, Sum.inr.injEq, Prod.mk.injEq, hlk, hn, if_false, ite_self, add_zero]
      split_ifs <;> simp_all
    · simp only [mixedScalarWitness, dif_neg hk, add_zero, coeff_ite, coeff_X_pow,
        coeff_zero, Sum.inr.injEq, Prod.mk.injEq, hlk]
      split_ifs <;> simp_all

theorem mixedScalarWitness_mul_coeff_low_left (b : H)
    (f : Fin s ↪ MixedScalarSlots (L := L) b) (E : Matrix H (MixedScalarRows a L H) K)
    (l : Fin a) (i : H) (j : L) :
    ((E.map C * mixedScalarWitness (a := a) (K := K) b f) i (Sum.inl j)).coeff l.val =
      E i (Sum.inl (l,j)) := by
  simp only [Matrix.mul_apply, finset_sum_coeff, Matrix.map_apply, coeff_C_mul,
    mixedScalarWitness_coeff_low_left]
  simp [mul_ite]

theorem mixedScalarWitness_mul_coeff_low_right (b : H)
    (f : Fin s ↪ MixedScalarSlots (L := L) b) (E : Matrix H (MixedScalarRows a L H) K)
    (l : Fin (a+1)) (i j : H) :
    ((E.map C * mixedScalarWitness (a := a) (K := K) b f) i (Sum.inr j)).coeff l.val =
      E i (Sum.inr (l,j)) := by
  simp only [Matrix.mul_apply, finset_sum_coeff, Matrix.map_apply, coeff_C_mul,
    mixedScalarWitness_coeff_low_right]
  simp [mul_ite]

omit [Fintype L] [Fintype H] in
theorem mixedScalarWitness_coeff_high (b : H) (f : Fin s ↪ MixedScalarSlots (L := L) b)
    (t : Fin 3) (j : L ⊕ H) (x : MixedScalarRows a L H) :
    (mixedScalarWitness (K := K) b f x j).coeff (a + mixedColumnShift j + t.val) =
      match x with
      | Sum.inl _ => 0
      | Sum.inr x => if h : x.1.val < s then
          if (f ⟨x.1.val,h⟩).1 = t ∧ x.2 = (f ⟨x.1.val,h⟩).2.val.1 ∧
            j = (f ⟨x.1.val,h⟩).2.val.2 then 1 else 0 else 0 := by
  cases x with
  | inl x =>
    have hn : a + mixedColumnShift j + t.val ≠ x.1.val := by have := x.1.isLt; omega
    simp [mixedScalarWitness, coeff_ite, coeff_X_pow, hn]
  | inr x =>
    have hbase : (if Sum.inr x.2 = j then (X : K[X])^x.1.val else 0).coeff
        (a + mixedColumnShift j + t.val) = 0 := by
      cases j with
      | inl j => simp
      | inr j =>
        have hn : a + mixedColumnShift (Sum.inr j : L ⊕ H) + t.val ≠ x.1.val := by
          have := x.1.isLt; simp only [mixedColumnShift, Sum.elim_inr]; omega
        simp [coeff_ite, coeff_X_pow, hn]
    simp only [mixedScalarWitness, coeff_add, hbase, zero_add]
    by_cases hx : x.1.val < s
    · have ht : (a + mixedColumnShift j + t.val =
          a + mixedColumnShift j + (f ⟨x.1.val,hx⟩).1.val) ↔ (f ⟨x.1.val,hx⟩).1 = t := by
        rw [Nat.add_left_cancel_iff, Fin.val_inj]; exact eq_comm
      simp only [dif_pos hx, coeff_ite, coeff_X_pow, coeff_zero, ht]
      split_ifs <;> simp_all
    · simp [hx]

theorem mixedScalarWitness_mul_coeff_high (b : H)
    (f : Fin s ↪ MixedScalarSlots (L := L) b) (E : Matrix H (MixedScalarRows a L H) K)
    (t : Fin 3) (i : H) (j : L ⊕ H) :
    ((E.map C * mixedScalarWitness (a := a) (K := K) b f) i j).coeff
        (a + mixedColumnShift j + t.val) =
      ∑ k : Fin (a+1), if h : k.val < s then
        if (f ⟨k.val,h⟩).1 = t ∧ j = (f ⟨k.val,h⟩).2.val.2
        then E i (Sum.inr (k,(f ⟨k.val,h⟩).2.val.1)) else 0 else 0 := by
  simp only [Matrix.mul_apply, finset_sum_coeff, Matrix.map_apply, coeff_C_mul,
    mixedScalarWitness_coeff_high, Fintype.sum_sum_type, Fintype.sum_prod_type, coeff_add,
    mul_zero, Finset.sum_const_zero, zero_add]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hks : k.val < s
  · simp only [dif_pos hks]
    by_cases ht : (f ⟨k.val,hks⟩).1 = t <;>
      by_cases hj : j = (f ⟨k.val,hks⟩).2.val.2 <;> simp [ht, hj, mul_ite, Finset.sum_ite_eq']
    exact Fintype.sum_ite_eq' ((f ⟨k.val,hks⟩).2.val.1)
      (fun x => E i (Sum.inr (k,x)))
  · simp [hks]

theorem mixedScalarWitness_scalar_obstruction (b : H)
    (f : Fin s ↪ MixedScalarSlots (L := L) b) (E : Matrix H (MixedScalarRows a L H) K)
    (c : K[X])
    (hrel : E.map C * mixedScalarWitness (a := a) (K := K) b f =
      (-c) • (fun i j => if Sum.inr i = j then 1 else 0 : Matrix H (L ⊕ H) K[X]))
    (htail : ∀ l : Fin (a+1), s ≤ l.val → c.coeff l.val = 0) : E = 0 ∧ c = 0 := by
  have hcoeff (d : ℕ) (i : H) (j : L ⊕ H) :
      ((E.map C * mixedScalarWitness (a := a) (K := K) b f) i j).coeff d =
        if Sum.inr i = j then -(c.coeff d) else 0 := by
    have h := congrArg (fun A : Matrix H (L ⊕ H) K[X] => (A i j).coeff d) hrel
    simpa [Matrix.smul_apply, mul_ite, coeff_ite] using h
  have hleft (l : Fin a) (i : H) (j : L) : E i (Sum.inl (l,j)) = 0 := by
    rw [← mixedScalarWitness_mul_coeff_low_left b f E l i j]
    simpa using hcoeff l.val i (Sum.inl j)
  have hright (l : Fin (a+1)) (i j : H) :
      E i (Sum.inr (l,j)) = if i = j then -(c.coeff l.val) else 0 := by
    rw [← mixedScalarWitness_mul_coeff_low_right b f E l i j]
    simpa using hcoeff l.val i (Sum.inr j)
  have hhigh (t : Fin 3) (i : H) (j : L ⊕ H) :
      (∑ k : Fin (a+1), if h : k.val < s then
        if (f ⟨k.val,h⟩).1 = t ∧ i = (f ⟨k.val,h⟩).2.val.1 ∧
          j = (f ⟨k.val,h⟩).2.val.2 then -(c.coeff k.val) else 0 else 0) =
        if Sum.inr i = j then -(c.coeff (a+mixedColumnShift j+t.val)) else 0 := by
    have h := hcoeff (a+mixedColumnShift j+t.val) i j
    rw [mixedScalarWitness_mul_coeff_high] at h
    convert h using 1
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hks : k.val < s
    · simp only [dif_pos hks, hright]
      split_ifs <;> simp_all
    · simp [hks]
  have htop (t : Fin 3) : c.coeff (a+1+t.val) = 0 := by
    have h := hhigh t b (Sum.inr b)
    have hz : ∀ k : Fin (a+1), (if h : k.val < s then
        if (f ⟨k.val,h⟩).1 = t ∧ b = (f ⟨k.val,h⟩).2.val.1 ∧
          Sum.inr b = (f ⟨k.val,h⟩).2.val.2 then -(c.coeff k.val) else 0 else 0) = 0 := by
      intro k
      split_ifs with hks hk
      · exact False.elim ((f ⟨k.val,hks⟩).2.property
          (Prod.ext hk.2.1.symm hk.2.2.symm))
      all_goals rfl
    simpa only [hz, Finset.sum_const_zero, if_true, mixedColumnShift, Sum.elim_inr,
      neg_eq_zero] using h.symm
  have hclow (l : Fin (a+1)) : c.coeff l.val = 0 := by
    by_cases hls : l.val < s
    · let l' : Fin s := ⟨l.val,hls⟩
      have h := hhigh (f l').1 (f l').2.val.1 (f l').2.val.2
      have hi (k : Fin (a+1)) :
          (if h : k.val < s then
            if (f ⟨k.val,h⟩).1 = (f l').1 ∧
              (f l').2.val.1 = (f ⟨k.val,h⟩).2.val.1 ∧
              (f l').2.val.2 = (f ⟨k.val,h⟩).2.val.2
            then -(c.coeff k.val) else 0 else 0) =
          if k = l then -(c.coeff k.val) else 0 := by
        by_cases hks : k.val < s
        · have heq : ((f ⟨k.val,hks⟩).1 = (f l').1 ∧
              (f l').2.val.1 = (f ⟨k.val,hks⟩).2.val.1 ∧
              (f l').2.val.2 = (f ⟨k.val,hks⟩).2.val.2) ↔ k = l := by
            constructor
            · intro hk
              have hh := f.injective (Prod.ext hk.1 (Subtype.ext
                (Prod.ext hk.2.1.symm hk.2.2.symm)))
              exact Fin.ext (congrArg (fun v : Fin s => v.val) hh)
            · rintro rfl
              exact ⟨rfl,rfl,rfl⟩
          simp only [dif_pos hks, heq]
        · have hkl : k ≠ l := by rintro rfl; exact hks hls
          simp [hks,hkl]
      simp only [hi, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
      cases hj : (f l').2.val.2 with
      | inl j => simpa [hj] using h
      | inr j => simpa [hj, mixedColumnShift, htop] using h
    · exact htail l (by omega)
  have hE : E = 0 := by
    funext i x
    cases x with
    | inl x => exact hleft x.1 i x.2
    | inr x => simp [hright,hclow]
  refine ⟨hE,?_⟩
  have h := congrArg (fun A : Matrix H (L ⊕ H) K[X] => A b (Sum.inr b)) hrel
  simpa [hE] using h.symm

theorem mixedScalarWitness_eval_zero_injective (b : H)
    (f : Fin s ↪ MixedScalarSlots (L := L) b) (ha : 0 < a) :
    Function.Injective
      ((mixedScalarWitness (a := a) (K := K) b f).map (Polynomial.evalRingHom 0)).mulVec := by
  intro u v huv
  funext i
  cases i with
  | inl i =>
    let z : Fin a := ⟨0,ha⟩
    have h := congrFun huv (Sum.inl (z,i))
    have hrow (j : L ⊕ H) :
        Polynomial.eval 0 (mixedScalarWitness (K := K) b f (Sum.inl (z,i)) j) =
          if Sum.inl i = j then 1 else 0 := by
      simp only [mixedScalarWitness,z,pow_zero]
      split_ifs <;> simp
    simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply, Polynomial.coe_evalRingHom,
      hrow, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true] using h

  | inr i =>
    let z : Fin (a+1) := ⟨0,by omega⟩
    have h := congrFun huv (Sum.inr (z,i))
    have hrow (j : L ⊕ H) :
        Polynomial.eval 0 (mixedScalarWitness (K := K) b f (Sum.inr (z,i)) j) =
          if Sum.inr i = j then 1 else 0 := by
      simp only [mixedScalarWitness, z, pow_zero, Polynomial.eval_add]
      split_ifs <;> simp_all [Nat.ne_of_gt ha]
    simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply, Polynomial.coe_evalRingHom,
      hrow, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true] using h

theorem mixedScalarWitness_injective (b : H)
    (f : Fin s ↪ MixedScalarSlots (L := L) b) (ha : 0 < a) :
    Function.Injective (mixedScalarWitness (a := a) (K := K) b f).mulVec := by
  apply polynomial_matrix_injective_of_zero
  exact mixedScalarWitness_eval_zero_injective b f ha

theorem mixedScalarWitness_polynomial_scalar_obstruction (b : H)
    (f : Fin s ↪ MixedScalarSlots (L := L) b)
    (E : Matrix H (MixedScalarRows a L H) K[X]) (c : K[X])
    (hE : DegreeBound E 0)
    (hrel : E * mixedScalarWitness (a := a) (K := K) b f =
      (-c) • (fun i j => if Sum.inr i = j then 1 else 0 : Matrix H (L ⊕ H) K[X]))
    (htail : ∀ l : Fin (a+1), s ≤ l.val → c.coeff l.val = 0) : E = 0 ∧ c = 0 := by
  let E₀ : Matrix H (MixedScalarRows a L H) K := fun i j => (E i j).coeff 0
  have he : E = E₀.map C := by
    funext i j
    exact eq_C_of_natDegree_le_zero (hE i j)
  obtain ⟨hz,hc⟩ := mixedScalarWitness_scalar_obstruction b f E₀ c (by rwa [← he]) htail
  refine ⟨?_,hc⟩
  rw [he,hz]
  simp

theorem mixedScalarSlots_card (b : H) :
    Fintype.card (MixedScalarSlots (L := L) b) =
      3 * (Fintype.card H * (Fintype.card L + Fintype.card H) - 1) := by
  simp [MixedScalarSlots, Fintype.card_subtype_compl]

theorem mixedScalarWitness_mixed_scalar_obstruction (b : H)
    (f : Fin s ↪ MixedScalarSlots (L := L) b)
    (E : Matrix (L ⊕ H) (MixedScalarRows a L H) K[X]) (c : K[X])
    (hE : ∀ i j, (E (Sum.inr i) j).natDegree ≤ 0)
    (hrel : E * mixedScalarWitness (a := a) (K := K) b f = (-c) • 1)
    (htail : ∀ l : Fin (a+1), s ≤ l.val → c.coeff l.val = 0) : c = 0 := by
  let E' : Matrix H (MixedScalarRows a L H) K[X] := E.submatrix Sum.inr id
  have hrel' : E' * mixedScalarWitness (a := a) (K := K) b f =
      (-c) • (fun i j => if Sum.inr i = j then 1 else 0 : Matrix H (L ⊕ H) K[X]) := by
    funext i j
    have h := congrArg (fun A : Matrix (L ⊕ H) (L ⊕ H) K[X] => A (Sum.inr i) j) hrel
    simpa [E', Matrix.mul_apply, Matrix.one_apply] using h
  exact (mixedScalarWitness_polynomial_scalar_obstruction b f E' c hE hrel' htail).2

omit [DecidableEq L] [DecidableEq H] in
theorem mixedScalarRows_card :
    Fintype.card (MixedScalarRows a L H) =
      a * (Fintype.card L + Fintype.card H) + Fintype.card H := by
  simp [MixedScalarRows]
  ring

theorem mixedScalarTail_dimension (a u v : ℕ) (hv : 0 < v) :
    (a+1) - 3 * (v * (u+v) - 1) = a+4 - 3 * (u+v) * v := by
  have hp : 0 < v * (u+v) := Nat.mul_pos hv (by omega)
  have he : 3 * (v * (u+v) - 1) = 3 * (v * (u+v)) - 3 := by omega
  have hc : 3 * (v * (u+v)) = 3 * (u+v) * v := by ring
  rw [he,hc]
  have hp' : 3 ≤ 3 * (u+v) * v := by rw [← hc]; omega
  omega

theorem exists_mixed_scalar_witness_eval_zero (a u v : ℕ) (ha : 0 < a) (hv : 0 < v) :
    ∃ G : Matrix (MixedScalarRows a (Fin u) (Fin v)) (Fin u ⊕ Fin v) K[X],
      (∀ x j, (G x j).natDegree ≤ a + mixedColumnShift j + 2) ∧
      Function.Injective G.mulVec ∧
      Function.Injective (G.map (Polynomial.evalRingHom 0)).mulVec ∧
      ∀ (E : Matrix (Fin v) (MixedScalarRows a (Fin u) (Fin v)) K) (c : K[X]),
        E.map C * G = (-c) •
          (fun i j => if Sum.inr i = j then 1 else 0 : Matrix (Fin v) (Fin u ⊕ Fin v) K[X]) →
        (∀ l : Fin ((a+1) - 3 * (v * (u+v) - 1)),
          c.coeff (3 * (v * (u+v) - 1) + l.val) = 0) → E = 0 ∧ c = 0 := by
  let b : Fin v := ⟨0,hv⟩
  let N := 3 * (v * (u+v) - 1)
  let s := min (a+1) N
  have hcard : s ≤ Fintype.card (MixedScalarSlots (L := Fin u) b) := by
    simp [mixedScalarSlots_card, s, N]
  let f : Fin s ↪ MixedScalarSlots (L := Fin u) b :=
    { toFun := fun i => (Fintype.equivFin _).symm ⟨i.val, lt_of_lt_of_le i.isLt hcard⟩
      inj' := by
        intro i j hij
        have h := (Fintype.equivFin _).symm.injective hij
        exact Fin.ext (congrArg
          (fun x : Fin (Fintype.card (MixedScalarSlots (L := Fin u) b)) => x.val) h) }
  refine ⟨mixedScalarWitness b f, mixedScalarWitness_degree b f,
    mixedScalarWitness_injective b f ha, mixedScalarWitness_eval_zero_injective b f ha, ?_⟩
  intro E c hrel htail
  apply mixedScalarWitness_scalar_obstruction b f E c hrel
  intro l hl
  have hN : N ≤ l.val := by have := l.isLt; dsimp [s] at hl; omega
  let k : Fin ((a+1) - N) := ⟨l.val - N, by have := l.isLt; omega⟩
  have hk : N + k.val = l.val := by dsimp [k]; omega
  simpa only [← hk] using htail k

theorem exists_mixed_scalar_witness (a u v : ℕ) (ha : 0 < a) (hv : 0 < v) :
    ∃ G : Matrix (MixedScalarRows a (Fin u) (Fin v)) (Fin u ⊕ Fin v) K[X],
      (∀ x j, (G x j).natDegree ≤ a + mixedColumnShift j + 2) ∧
      Function.Injective G.mulVec ∧
      ∀ (E : Matrix (Fin v) (MixedScalarRows a (Fin u) (Fin v)) K) (c : K[X]),
        E.map C * G = (-c) •
          (fun i j => if Sum.inr i = j then 1 else 0 : Matrix (Fin v) (Fin u ⊕ Fin v) K[X]) →
        (∀ l : Fin ((a+1) - 3 * (v * (u+v) - 1)),
          c.coeff (3 * (v * (u+v) - 1) + l.val) = 0) → E = 0 ∧ c = 0 := by
  obtain ⟨G,hG,hi,_,hz⟩ := exists_mixed_scalar_witness_eval_zero (K := K) a u v ha hv
  exact ⟨G,hG,hi,hz⟩

end FD56

