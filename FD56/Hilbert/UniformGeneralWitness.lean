/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.UniformSLWitness

/-! Matrix-unit witnesses for an arbitrary number of uniform blocks. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K r : Type*} [Field K] [Fintype r] [DecidableEq r] {a : ℕ}

abbrev UniformWitnessSlots (b : r) := Fin 3 × {p : r × r // p ≠ (b, b)}

def uniformGeneralWitness (b : r) (f : Fin a ↪ UniformWitnessSlots b) :
    Matrix (Fin a × r) r K[X] := fun x j =>
  (if x.2 = j then X ^ x.1.val else 0) +
    (if x.2 = (f x.1).2.val.1 ∧ j = (f x.1).2.val.2
      then X ^ (a + (f x.1).1.val) else 0)

omit [Fintype r] in
theorem uniformGeneralWitness_degree (b : r) (f : Fin a ↪ UniformWitnessSlots b) :
    DegreeBound (uniformGeneralWitness (K := K) b f) (a + 2) := by
  intro x j
  apply natDegree_add_le_of_degree_le
  · split_ifs
    · exact (natDegree_X_pow_le _).trans (by have := x.1.isLt; omega)
    · simp
  · split_ifs
    · exact (natDegree_X_pow_le _).trans (by have := (f x.1).1.isLt; omega)
    · simp

theorem uniformGeneralWitness_injective (b : r) (f : Fin a ↪ UniformWitnessSlots b)
    (ha : 0 < a) : Function.Injective (uniformGeneralWitness (K := K) b f).mulVec := by
  apply polynomial_matrix_injective_of_zero
  intro u v huv
  funext i
  let z : Fin a := ⟨0, ha⟩
  have h := congrFun huv (z, i)
  have hrow (j : r) : Polynomial.eval 0 (uniformGeneralWitness (K := K) b f (z, i) j) =
      if i = j then 1 else 0 := by
    have hn : a + (f z).1.val ≠ 0 := by omega
    simp only [uniformGeneralWitness, z, pow_zero, Polynomial.eval_add]
    split_ifs <;> simp_all [z, Nat.ne_of_gt ha]
  simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply, Polynomial.coe_evalRingHom,
    hrow, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true] using h

private theorem coeff_ite (b : Prop) [Decidable b] (p q : K[X]) (d : ℕ) :
    (if b then p else q).coeff d = if b then p.coeff d else q.coeff d := by
  split_ifs <;> rfl

omit [Fintype r] in
theorem uniformGeneralWitness_coeff_low (b : r) (f : Fin a ↪ UniformWitnessSlots b)
    (l k : Fin a) (i j : r) :
    (uniformGeneralWitness (K := K) b f (k,i) j).coeff l.val =
      if k = l ∧ i = j then 1 else 0 := by
  have hn : l.val ≠ a + (f k).1.val := by have := l.isLt; omega
  have hlk : (l.val = k.val) ↔ k = l := by rw [Fin.val_inj]; exact eq_comm
  simp only [uniformGeneralWitness, coeff_add, coeff_ite, coeff_X_pow, coeff_zero, hn,
    hlk, if_false, ite_self, add_zero]
  split_ifs <;> simp_all

theorem uniformGeneralWitness_mul_coeff_low (b : r)
    (f : Fin a ↪ UniformWitnessSlots b) (E : Matrix r (Fin a × r) K)
    (l : Fin a) (i j : r) :
    ((E.map Polynomial.C * uniformGeneralWitness (K := K) b f) i j).coeff l.val = E i (l,j) := by
  simp only [Matrix.mul_apply, finset_sum_coeff, Matrix.map_apply, coeff_C_mul,
    Fintype.sum_prod_type, uniformGeneralWitness_coeff_low]
  simp only [ite_and]
  simp [mul_ite]

omit [Fintype r] in
theorem uniformGeneralWitness_coeff_high (b : r) (f : Fin a ↪ UniformWitnessSlots b)
    (t : Fin 3) (k : Fin a) (i j : r) :
    (uniformGeneralWitness (K := K) b f (k,i) j).coeff (a + t.val) =
      if (f k).1 = t ∧ i = (f k).2.val.1 ∧ j = (f k).2.val.2 then 1 else 0 := by
  have hn : a + t.val ≠ k.val := by have := k.isLt; omega
  have ht : (a + t.val = a + (f k).1.val) ↔ (f k).1 = t := by
    rw [Nat.add_left_cancel_iff, Fin.val_inj]; exact eq_comm
  simp only [uniformGeneralWitness, coeff_add, coeff_ite, coeff_X_pow, coeff_zero, hn,
    ht, if_false, ite_self, zero_add]
  split_ifs <;> simp_all

theorem uniformGeneralWitness_mul_coeff_high (b : r)
    (f : Fin a ↪ UniformWitnessSlots b) (E : Matrix r (Fin a × r) K)
    (t : Fin 3) (i j : r) :
    ((E.map Polynomial.C * uniformGeneralWitness (K := K) b f) i j).coeff (a+t.val) =
      ∑ k : Fin a, if (f k).1 = t ∧ j = (f k).2.val.2
        then E i (k, (f k).2.val.1) else 0 := by
  simp only [Matrix.mul_apply, finset_sum_coeff, Matrix.map_apply, coeff_C_mul,
    Fintype.sum_prod_type, uniformGeneralWitness_coeff_high]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases ht : (f k).1 = t <;> by_cases hj : j = (f k).2.val.2 <;>
    simp [ht, hj, mul_ite]

theorem uniformGeneralWitness_constant_matrix_obstruction (b : r)
    (f : Fin a ↪ UniformWitnessSlots b) (E : Matrix r (Fin a × r) K) (c : K[X])
    (hrel : E.map Polynomial.C * uniformGeneralWitness (K := K) b f =
      (-c) • (1 : Matrix r r K[X])) : E = 0 ∧ c = 0 := by
  have hcoeff (d : ℕ) (i j : r) :
      ((E.map Polynomial.C * uniformGeneralWitness (K := K) b f) i j).coeff d =
        if i = j then -(c.coeff d) else 0 := by
    have h := congrArg (fun A : Matrix r r K[X] => (A i j).coeff d) hrel
    simpa [Matrix.smul_apply, Matrix.one_apply, mul_ite, coeff_ite] using h
  have hlow (l : Fin a) (i j : r) :
      E i (l,j) = if i = j then -(c.coeff l.val) else 0 := by
    rw [← uniformGeneralWitness_mul_coeff_low b f E l i j]
    exact hcoeff l.val i j
  have hhigh (t : Fin 3) (i j : r) :
      (∑ k : Fin a, if (f k).1 = t ∧ i = (f k).2.val.1 ∧ j = (f k).2.val.2
        then -(c.coeff k.val) else 0) = if i = j then -(c.coeff (a+t.val)) else 0 := by
    have h := hcoeff (a+t.val) i j
    rw [uniformGeneralWitness_mul_coeff_high] at h
    convert h using 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [hlow]
    split_ifs <;> simp_all
  have htop (t : Fin 3) : c.coeff (a+t.val) = 0 := by
    have h := hhigh t b b
    have hz : ∀ k : Fin a, ¬((f k).1 = t ∧ b = (f k).2.val.1 ∧ b = (f k).2.val.2) := by
      intro k hk
      apply (f k).2.property
      exact Prod.ext hk.2.1.symm hk.2.2.symm
    simpa [hz] using h.symm
  have hclow (l : Fin a) : c.coeff l.val = 0 := by
    have h := hhigh (f l).1 (f l).2.val.1 (f l).2.val.2
    have hi (k : Fin a) :
        ((f k).1 = (f l).1 ∧ (f l).2.val.1 = (f k).2.val.1 ∧
          (f l).2.val.2 = (f k).2.val.2) ↔ k = l := by
      constructor
      · intro hk
        apply f.injective
        apply Prod.ext hk.1
        apply Subtype.ext
        exact Prod.ext hk.2.1.symm hk.2.2.symm
      · rintro rfl
        exact ⟨rfl,rfl,rfl⟩
    simpa [hi, htop] using h
  have hE : E = 0 := by
    funext i x
    rcases x with ⟨l,j⟩
    simp [hlow, hclow]
  refine ⟨hE, ?_⟩
  have h := congrArg (fun A : Matrix r r K[X] => A b b) hrel
  simpa [hE] using h.symm

theorem uniformGeneralWitness_constant_scalar_obstruction (b : r)
    (f : Fin a ↪ UniformWitnessSlots b) (E : Matrix r (Fin a × r) K[X]) (c : K[X])
    (hE : DegreeBound E 0)
    (hrel : E * uniformGeneralWitness b f = (-c) • (1 : Matrix r r K[X])) :
    E = 0 ∧ c = 0 := by
  let E₀ : Matrix r (Fin a × r) K := fun i j => (E i j).coeff 0
  have he : E = E₀.map Polynomial.C := by
    funext i j
    exact eq_C_of_natDegree_le_zero (hE i j)
  obtain ⟨hz,hc⟩ := uniformGeneralWitness_constant_matrix_obstruction b f E₀ c (by
    rwa [← he])
  refine ⟨?_,hc⟩
  rw [he,hz]
  simp

theorem uniformWitnessSlots_card (b : r) :
    Fintype.card (UniformWitnessSlots b) = 3 * (Fintype.card r ^ 2 - 1) := by
  simp [UniformWitnessSlots, Fintype.card_subtype_compl, pow_two]

theorem exists_uniform_general_sl_witness (a r : ℕ) (ha : 0 < a) (hr : 0 < r)
    (hcap : a ≤ 3 * (r ^ 2 - 1)) :
    ∃ G : Matrix (Fin a × Fin r) (Fin r) K[X], DegreeBound G (a+2) ∧
      Function.Injective G.mulVec ∧
      ∀ (E : Matrix (Fin r) (Fin a × Fin r) K[X]) (c : K[X]),
        DegreeBound E 0 → E * G = (-c) • 1 → E = 0 ∧ c = 0 := by
  let b : Fin r := ⟨0,hr⟩
  have hcard : a ≤ Fintype.card (UniformWitnessSlots b) := by
    simpa [uniformWitnessSlots_card, pow_two] using hcap
  let f : Fin a ↪ UniformWitnessSlots b :=
    { toFun := fun i => (Fintype.equivFin _).symm ⟨i.val, lt_of_lt_of_le i.isLt hcard⟩
      inj' := by
        intro i j hij
        have h := (Fintype.equivFin _).symm.injective hij
        exact Fin.ext (congrArg (fun x : Fin (Fintype.card (UniformWitnessSlots b)) => x.val) h) }
  exact ⟨uniformGeneralWitness b f, uniformGeneralWitness_degree b f,
    uniformGeneralWitness_injective b f ha, uniformGeneralWitness_constant_scalar_obstruction b f⟩

end FD56
