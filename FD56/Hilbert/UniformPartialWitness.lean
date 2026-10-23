/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.UniformGeneralWitness

/-! Uniform witnesses whose relations are determined by the unassigned scalar coefficients. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K r : Type*} [Field K] [Fintype r] [DecidableEq r] {a s : ℕ}

def uniformPartialWitness (b : r) (f : Fin s ↪ UniformWitnessSlots b) :
    Matrix (Fin a × r) r K[X] := fun x j =>
  (if x.2 = j then X ^ x.1.val else 0) +
    (if h : x.1.val < s then
      if x.2 = (f ⟨x.1.val,h⟩).2.val.1 ∧ j = (f ⟨x.1.val,h⟩).2.val.2
      then X ^ (a + (f ⟨x.1.val,h⟩).1.val) else 0 else 0)

omit [Fintype r] in
theorem uniformPartialWitness_degree (b : r) (f : Fin s ↪ UniformWitnessSlots b) :
    DegreeBound (uniformPartialWitness (a := a) (K := K) b f) (a + 2) := by
  intro x j
  apply natDegree_add_le_of_degree_le
  · split_ifs
    · exact (natDegree_X_pow_le _).trans (by have := x.1.isLt; omega)
    · simp
  · split_ifs with h
    · exact (natDegree_X_pow_le _).trans (by have := (f ⟨x.1.val,h⟩).1.isLt; omega)
    all_goals simp

theorem uniformPartialWitness_injective (b : r) (f : Fin s ↪ UniformWitnessSlots b)
    (ha : 0 < a) : Function.Injective (uniformPartialWitness (a := a) (K := K) b f).mulVec := by
  apply polynomial_matrix_injective_of_zero
  intro u v huv
  funext i
  let z : Fin a := ⟨0,ha⟩
  have h := congrFun huv (z,i)
  have hrow (j : r) : Polynomial.eval 0 (uniformPartialWitness (K := K) b f (z,i) j) =
      if i = j then 1 else 0 := by
    simp only [uniformPartialWitness, z, pow_zero, Polynomial.eval_add]
    split_ifs <;> simp_all [Nat.ne_of_gt ha]
  simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply, Polynomial.coe_evalRingHom,
    hrow, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true] using h

private theorem coeff_ite (p : Prop) [Decidable p] (f g : K[X]) (d : ℕ) :
    (if p then f else g).coeff d = if p then f.coeff d else g.coeff d := by
  split_ifs <;> rfl

omit [Fintype r] in
theorem uniformPartialWitness_coeff_low (b : r) (f : Fin s ↪ UniformWitnessSlots b)
    (l k : Fin a) (i j : r) :
    (uniformPartialWitness (K := K) b f (k,i) j).coeff l.val =
      if k = l ∧ i = j then 1 else 0 := by
  have hlk : (l.val = k.val) ↔ k = l := by rw [Fin.val_inj]; exact eq_comm
  by_cases hk : k.val < s
  · have hn : l.val ≠ a + (f ⟨k.val,hk⟩).1.val := by have := l.isLt; omega
    simp only [uniformPartialWitness, dif_pos hk, coeff_add, coeff_ite, coeff_X_pow,
      coeff_zero, hn, hlk, if_false, ite_self, add_zero]
    split_ifs <;> simp_all
  · simp only [uniformPartialWitness, dif_neg hk, add_zero, coeff_ite, coeff_X_pow,
      coeff_zero, hlk]
    split_ifs <;> simp_all

theorem uniformPartialWitness_mul_coeff_low (b : r)
    (f : Fin s ↪ UniformWitnessSlots b) (E : Matrix r (Fin a × r) K)
    (l : Fin a) (i j : r) :
    ((E.map Polynomial.C * uniformPartialWitness (a := a) (K := K) b f) i j).coeff l.val = E i (l,j) := by
  simp only [Matrix.mul_apply, finset_sum_coeff, Matrix.map_apply, coeff_C_mul,
    Fintype.sum_prod_type, uniformPartialWitness_coeff_low, ite_and]
  simp [mul_ite]

omit [Fintype r] in
theorem uniformPartialWitness_coeff_high (b : r) (f : Fin s ↪ UniformWitnessSlots b)
    (t : Fin 3) (k : Fin a) (i j : r) :
    (uniformPartialWitness (K := K) b f (k,i) j).coeff (a + t.val) =
      if h : k.val < s then
        if (f ⟨k.val,h⟩).1 = t ∧ i = (f ⟨k.val,h⟩).2.val.1 ∧
          j = (f ⟨k.val,h⟩).2.val.2 then 1 else 0 else 0 := by
  have hn : a + t.val ≠ k.val := by have := k.isLt; omega
  by_cases hk : k.val < s
  · have ht : (a + t.val = a + (f ⟨k.val,hk⟩).1.val) ↔ (f ⟨k.val,hk⟩).1 = t := by
      rw [Nat.add_left_cancel_iff, Fin.val_inj]; exact eq_comm
    simp only [uniformPartialWitness, dif_pos hk, coeff_add, coeff_ite, coeff_X_pow,
      coeff_zero, hn, ht, if_false, ite_self, zero_add]
    split_ifs <;> simp_all
  · simp [uniformPartialWitness, hk, coeff_ite, coeff_X_pow, hn]

theorem uniformPartialWitness_mul_coeff_high (b : r)
    (f : Fin s ↪ UniformWitnessSlots b) (E : Matrix r (Fin a × r) K)
    (t : Fin 3) (i j : r) :
    ((E.map Polynomial.C * uniformPartialWitness (a := a) (K := K) b f) i j).coeff (a+t.val) =
      ∑ k : Fin a, if h : k.val < s then
        if (f ⟨k.val,h⟩).1 = t ∧ j = (f ⟨k.val,h⟩).2.val.2
        then E i (k, (f ⟨k.val,h⟩).2.val.1) else 0 else 0 := by
  simp only [Matrix.mul_apply, finset_sum_coeff, Matrix.map_apply, coeff_C_mul,
    Fintype.sum_prod_type, uniformPartialWitness_coeff_high]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hks : k.val < s
  · simp only [dif_pos hks]
    by_cases ht : (f ⟨k.val,hks⟩).1 = t <;>
      by_cases hj : j = (f ⟨k.val,hks⟩).2.val.2 <;> simp [ht, hj, mul_ite]
  · simp [hks]

theorem uniformPartialWitness_constant_matrix_obstruction (b : r)
    (f : Fin s ↪ UniformWitnessSlots b) (E : Matrix r (Fin a × r) K) (c : K[X])
    (hrel : E.map Polynomial.C * uniformPartialWitness (a := a) (K := K) b f =
      (-c) • (1 : Matrix r r K[X]))
    (htail : ∀ l : Fin a, s ≤ l.val → c.coeff l.val = 0) : E = 0 ∧ c = 0 := by
  have hcoeff (d : ℕ) (i j : r) :
      ((E.map Polynomial.C * uniformPartialWitness (a := a) (K := K) b f) i j).coeff d =
        if i = j then -(c.coeff d) else 0 := by
    have h := congrArg (fun A : Matrix r r K[X] => (A i j).coeff d) hrel
    simpa [Matrix.smul_apply, Matrix.one_apply, mul_ite, coeff_ite] using h
  have hlow (l : Fin a) (i j : r) :
      E i (l,j) = if i = j then -(c.coeff l.val) else 0 := by
    rw [← uniformPartialWitness_mul_coeff_low b f E l i j]
    exact hcoeff l.val i j
  have hhigh (t : Fin 3) (i j : r) :
      (∑ k : Fin a, if h : k.val < s then
        if (f ⟨k.val,h⟩).1 = t ∧ i = (f ⟨k.val,h⟩).2.val.1 ∧
          j = (f ⟨k.val,h⟩).2.val.2 then -(c.coeff k.val) else 0 else 0) =
        if i = j then -(c.coeff (a+t.val)) else 0 := by
    have h := hcoeff (a+t.val) i j
    rw [uniformPartialWitness_mul_coeff_high] at h
    convert h using 1
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hks : k.val < s
    · simp only [dif_pos hks, hlow]
      split_ifs <;> simp_all
    · simp [hks]
  have htop (t : Fin 3) : c.coeff (a+t.val) = 0 := by
    have h := hhigh t b b
    have hz : ∀ k : Fin a, (if h : k.val < s then
        if (f ⟨k.val,h⟩).1 = t ∧ b = (f ⟨k.val,h⟩).2.val.1 ∧
          b = (f ⟨k.val,h⟩).2.val.2 then -(c.coeff k.val) else 0 else 0) = 0 := by
      intro k
      split_ifs with hks hk
      · exact False.elim ((f ⟨k.val,hks⟩).2.property
          (Prod.ext hk.2.1.symm hk.2.2.symm))
      all_goals rfl
    simpa only [hz, Finset.sum_const_zero, if_true, neg_eq_zero] using h.symm
  have hclow (l : Fin a) : c.coeff l.val = 0 := by
    by_cases hls : l.val < s
    · let l' : Fin s := ⟨l.val,hls⟩
      have h := hhigh (f l').1 (f l').2.val.1 (f l').2.val.2
      have hi (k : Fin a) :
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
      simpa [hi,htop] using h
    · exact htail l (by omega)
  have hE : E = 0 := by
    funext i x
    rcases x with ⟨l,j⟩
    simp [hlow,hclow]
  refine ⟨hE,?_⟩
  have h := congrArg (fun A : Matrix r r K[X] => A b b) hrel
  simpa [hE] using h.symm

theorem uniformPartialWitness_constant_scalar_obstruction (b : r)
    (f : Fin s ↪ UniformWitnessSlots b) (E : Matrix r (Fin a × r) K[X]) (c : K[X])
    (hE : DegreeBound E 0)
    (hrel : E * uniformPartialWitness (a := a) b f = (-c) • (1 : Matrix r r K[X]))
    (htail : ∀ l : Fin a, s ≤ l.val → c.coeff l.val = 0) : E = 0 ∧ c = 0 := by
  let E₀ : Matrix r (Fin a × r) K := fun i j => (E i j).coeff 0
  have he : E = E₀.map Polynomial.C := by
    funext i j
    exact eq_C_of_natDegree_le_zero (hE i j)
  obtain ⟨hz,hc⟩ := uniformPartialWitness_constant_matrix_obstruction b f E₀ c (by
    rwa [← he]) htail
  refine ⟨?_,hc⟩
  rw [he,hz]
  simp

theorem exists_uniform_partial_sl_witness (a r : ℕ) (ha : 0 < a) (hr : 0 < r) :
    ∃ G : Matrix (Fin a × Fin r) (Fin r) K[X], DegreeBound G (a+2) ∧
      Function.Injective G.mulVec ∧
      ∀ (E : Matrix (Fin r) (Fin a × Fin r) K[X]) (c : K[X]),
        DegreeBound E 0 → E * G = (-c) • 1 →
          (∀ l : Fin (a - 3 * (r ^ 2 - 1)), c.coeff (3 * (r ^ 2 - 1) + l.val) = 0) →
          E = 0 ∧ c = 0 := by
  let b : Fin r := ⟨0,hr⟩
  let N := 3 * (r ^ 2 - 1)
  let s := min a N
  have hcard : s ≤ Fintype.card (UniformWitnessSlots b) := by
    simpa [uniformWitnessSlots_card, pow_two, s, N] using (min_le_right a N)
  let f : Fin s ↪ UniformWitnessSlots b :=
    { toFun := fun i => (Fintype.equivFin _).symm ⟨i.val, lt_of_lt_of_le i.isLt hcard⟩
      inj' := by
        intro i j hij
        have h := (Fintype.equivFin _).symm.injective hij
        exact Fin.ext (congrArg (fun x : Fin (Fintype.card (UniformWitnessSlots b)) => x.val) h) }
  refine ⟨uniformPartialWitness b f, uniformPartialWitness_degree b f,
    uniformPartialWitness_injective b f ha, ?_⟩
  intro E c hE hrel htail
  apply uniformPartialWitness_constant_scalar_obstruction b f E c hE hrel
  intro l hl
  have hN : N ≤ l.val := by have := l.isLt; dsimp [s] at hl; omega
  let v : Fin (a - N) := ⟨l.val - N, by have := l.isLt; omega⟩
  have hv : N + v.val = l.val := by dsimp [v]; omega
  simpa only [← hv] using htail v

end FD56
