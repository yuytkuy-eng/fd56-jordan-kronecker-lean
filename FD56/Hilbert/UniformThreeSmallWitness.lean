/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.UniformThreeWitness

/-! A three-block witness whose affine scalar relations have three free coefficients. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K r : Type*} [Field K] [Fintype r] [DecidableEq r]

def uniformThreeSmallWitness (p q : r) : Matrix (Fin 3 × r) r K[X] := fun x j =>
  (if x.2 = j then X ^ (2*x.1.val) else 0) +
  (if x.1 = 0 ∧ x.2 = p ∧ j = p then X^5 else 0) +
  (if x.1 = 1 ∧ x.2 = p ∧ j = q then X^5 else 0) +
  (if x.1 = 2 ∧ x.2 = p ∧ j = q then X^5 else 0) +
  (if x.1 = 2 ∧ x.2 = q ∧ j = p then X^5 else 0)

omit [Fintype r] in
theorem uniformThreeSmallWitness_degree (p q : r) :
    DegreeBound (uniformThreeSmallWitness (K := K) p q) 5 := by
  intro x j
  unfold uniformThreeSmallWitness
  repeat apply natDegree_add_le_of_degree_le
  · split_ifs
    · exact (natDegree_X_pow_le _).trans (by have := x.1.isLt; omega)
    · simp
  all_goals split_ifs <;> simp

theorem uniformThreeSmallWitness_injective (p q : r) :
    Function.Injective (uniformThreeSmallWitness (K := K) p q).mulVec := by
  apply polynomial_matrix_injective_of_zero
  intro u v huv
  funext i
  have h := congrFun huv ((0 : Fin 3),i)
  have hrow (j : r) : Polynomial.eval 0 (uniformThreeSmallWitness (K := K) p q (0,i) j) =
      if i = j then 1 else 0 := by
    simp only [uniformThreeSmallWitness, Fin.val_zero, mul_zero, pow_zero, Polynomial.eval_add]
    split_ifs <;> simp_all
  simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply, Polynomial.coe_evalRingHom,
    hrow, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true] using h

private theorem uniformThreeSmallWitness_mul (p q : r)
    (E : Matrix r (Fin 3 × r) K[X]) (i j : r) :
    (E * uniformThreeSmallWitness (K := K) p q) i j =
      E i (0,j) + E i (1,j) * X^2 + E i (2,j) * X^4 +
      (if j = p then E i (0,p) else 0) * X^5 +
      (if j = q then E i (1,p) else 0) * X^5 +
      (if j = q then E i (2,p) else 0) * X^5 +
      (if j = p then E i (2,q) else 0) * X^5 := by
  simp [uniformThreeSmallWitness, Matrix.mul_apply, Fintype.sum_prod_type,
    Fin.sum_univ_succ, mul_add, mul_ite, Finset.sum_add_distrib, ite_mul, ite_and, add_assoc]

private theorem coeff_ite (p : Prop) [Decidable p] (f g : K[X]) (d : ℕ) :
    (if p then f else g).coeff d = if p then f.coeff d else g.coeff d := by
  split_ifs <;> rfl

theorem uniformThreeSmallWitness_scalar_obstruction (p q : r) (hpq : p ≠ q)
    (E : Matrix r (Fin 3 × r) K[X]) (c : K[X]) (hE : DegreeBound E 1)
    (hrel : E * uniformThreeSmallWitness p q = (-c) • (1 : Matrix r r K[X]))
    (hc0 : c.coeff 0 = 0) (hc2 : c.coeff 2 = 0) (hc4 : c.coeff 4 = 0) :
    E = 0 ∧ c = 0 := by
  have hcE (i : r) (x : Fin 3 × r) (k : ℕ) (hk : 1 < k) : (E i x).coeff k = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hE i x) hk)
  have hcoeff (d : ℕ) (i j : r) :
      ((E * uniformThreeSmallWitness (K := K) p q) i j).coeff d =
        if i = j then -(c.coeff d) else 0 := by
    have h := congrArg (fun A : Matrix r r K[X] => (A i j).coeff d) hrel
    simpa [Matrix.smul_apply, Matrix.one_apply, mul_ite, coeff_ite] using h
  have hlow0 (l : Fin 3) (i j : r) : (E i (l,j)).coeff 0 = 0 := by
    have h := hcoeff (2*l.val) i j
    fin_cases l <;> simpa [uniformThreeSmallWitness_mul, coeff_add, coeff_mul_X_pow',
      coeff_ite, hcE,hc0,hc2,hc4] using h
  have hlow1 (l : Fin 2) (i j : r) :
      (E i (Fin.castLE (by omega) l,j)).coeff 1 =
        if i = j then -(c.coeff (2*l.val+1)) else 0 := by
    have h := hcoeff (2*l.val+1) i j
    fin_cases l <;> simpa [uniformThreeSmallWitness_mul, coeff_add, coeff_mul_X_pow',
      coeff_ite, hcE] using h
  have hfive (i j : r) :
      (E i (2,j)).coeff 1 = if i = j then -(c.coeff 5) else 0 := by
    have h := hcoeff 5 i j
    simpa [uniformThreeSmallWitness_mul, coeff_add, coeff_mul_X_pow', coeff_ite,hcE,hlow0] using h
  have hsix (i j : r) :
      (if j = p then (E i (0,p)).coeff 1 else 0) +
      (if j = q then (E i (1,p)).coeff 1 else 0) +
      (if j = q then (E i (2,p)).coeff 1 else 0) +
      (if j = p then (E i (2,q)).coeff 1 else 0) =
      if i = j then -(c.coeff 6) else 0 := by
    have h := hcoeff 6 i j
    simpa [uniformThreeSmallWitness_mul, coeff_add, coeff_mul_X_pow', coeff_ite, hcE] using h
  have he0 (i j : r) : (E i (0,j)).coeff 1 = if i = j then -(c.coeff 1) else 0 :=
    hlow1 0 i j
  have he1 (i j : r) : (E i (1,j)).coeff 1 = if i = j then -(c.coeff 3) else 0 :=
    hlow1 1 i j
  have hc6 : c.coeff 6 = 0 := by
    simpa [he0,he1,hfive,hpq,Ne.symm hpq] using (hsix q q).symm
  have hc1 : c.coeff 1 = 0 := by
    simpa [he0,he1,hfive,hc6,hpq,Ne.symm hpq] using hsix p p
  have hc5 : c.coeff 5 = 0 := by
    simpa [he0,he1,hfive,hpq,Ne.symm hpq] using hsix q p
  have hc3 : c.coeff 3 = 0 := by
    simpa [he0,he1,hfive,hc5,hpq,Ne.symm hpq] using hsix p q
  have hzero : E = 0 := by
    funext i x
    rcases x with ⟨l,j⟩
    rw [eq_X_add_C_of_natDegree_le_one (hE i (l,j))]
    fin_cases l <;> simp [hlow0,he0,he1,hfive,hc1,hc3,hc5]
  refine ⟨hzero,?_⟩
  have h := congrArg (fun A : Matrix r r K[X] => A p p) hrel
  simpa [hzero] using h.symm

theorem exists_uniform_three_small_sl_witness :
    ∃ G : Matrix (Fin 3 × Fin 2) (Fin 2) K[X], DegreeBound G 5 ∧
      Function.Injective G.mulVec ∧
      ∀ (E : Matrix (Fin 2) (Fin 3 × Fin 2) K[X]) (c : K[X]),
        DegreeBound E 1 → E * G = (-c) • 1 →
          (∀ l : Fin 3, c.coeff (2*l.val) = 0) → E = 0 ∧ c = 0 := by
  refine ⟨uniformThreeSmallWitness 0 1, uniformThreeSmallWitness_degree 0 1,
    uniformThreeSmallWitness_injective 0 1, ?_⟩
  intro E c hE hrel hc
  exact uniformThreeSmallWitness_scalar_obstruction 0 1 (by decide) E c hE hrel
    (hc 0) (hc 1) (hc 2)

end FD56
