/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PolynomialMatrix
import FD56.LinearAlgebra.RankSpecialization

/-! A constant-row scalar obstruction for four equal rectangular blocks. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K r : Type*} [Field K] [Fintype r] [DecidableEq r]

/-- Four identity coefficient blocks, followed by four matrix-unit terms. -/
def uniformSLWitness (p q : r) : Matrix (Fin 4 × r) r K[X] := fun x j =>
  (if x.2 = j then X ^ x.1.val else 0) +
  (if x.1 = 0 ∧ x.2 = p ∧ j = p then X ^ 4 else 0) +
  (if x.1 = 1 ∧ x.2 = p ∧ j = q then X ^ 4 else 0) +
  (if x.1 = 2 ∧ x.2 = q ∧ j = p then X ^ 4 else 0) +
  (if x.1 = 3 ∧ x.2 = p ∧ j = p then X ^ 5 else 0)

omit [Fintype r] in
theorem uniformSLWitness_degree (p q : r) : DegreeBound (uniformSLWitness (K := K) p q) 6 := by
  intro x j
  unfold uniformSLWitness
  repeat apply natDegree_add_le_of_degree_le
  · split_ifs
    · exact (natDegree_X_pow_le _).trans (by have := x.1.isLt; omega)
    · simp
  all_goals split_ifs <;> simp

theorem uniformSLWitness_injective (p q : r) :
    Function.Injective (uniformSLWitness (K := K) p q).mulVec := by
  apply polynomial_matrix_injective_of_zero
  intro u v huv
  funext i
  have h := congrFun huv ((0 : Fin 4), i)
  have hrow (j : r) :
      Polynomial.eval 0 (uniformSLWitness (K := K) p q (0, i) j) =
        if i = j then 1 else 0 := by
    simp only [uniformSLWitness, Fin.val_zero, pow_zero, Polynomial.eval_add]
    split_ifs <;> simp_all
  simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply, Polynomial.coe_evalRingHom,
    hrow, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true] using h

private theorem polynomial_coeff_ite (b : Prop) [Decidable b] (f g : K[X]) (d : ℕ) :
    (if b then f else g).coeff d = if b then f.coeff d else g.coeff d := by
  split_ifs <;> rfl

private theorem uniformSLWitness_mul_coeff_low (p q : r)
    (E : Matrix r (Fin 4 × r) K) (l : Fin 4) (i j : r) :
    ((E.map Polynomial.C * uniformSLWitness (K := K) p q) i j).coeff l.val = E i (l, j) := by
  fin_cases l <;>
    simp [uniformSLWitness, Matrix.mul_apply, finset_sum_coeff, coeff_C_mul,
      coeff_add, coeff_X_pow, Fintype.sum_prod_type, Fin.sum_univ_succ,
      mul_add, mul_ite, Finset.sum_add_distrib, polynomial_coeff_ite]

private theorem uniformSLWitness_mul_coeff_four (p q : r) (hpq : p ≠ q)
    (E : Matrix r (Fin 4 × r) K) (i j : r) :
    ((E.map Polynomial.C * uniformSLWitness (K := K) p q) i j).coeff 4 =
      (if j = p then E i (0, p) else 0) +
      (if j = q then E i (1, p) else 0) +
      (if j = p then E i (2, q) else 0) := by
  by_cases hjp : j = p <;> by_cases hjq : j = q <;>
    simp [uniformSLWitness, Matrix.mul_apply, finset_sum_coeff, coeff_C_mul,
    coeff_add, coeff_X_pow, Fintype.sum_prod_type, Fin.sum_univ_succ,
    mul_add, mul_ite, Finset.sum_add_distrib, polynomial_coeff_ite, hjp, hjq, hpq, Ne.symm hpq]

private theorem uniformSLWitness_mul_coeff_five (p q : r)
    (E : Matrix r (Fin 4 × r) K) (i j : r) :
    ((E.map Polynomial.C * uniformSLWitness (K := K) p q) i j).coeff 5 =
      if j = p then E i (3, p) else 0 := by
  by_cases hjp : j = p <;>
    simp [uniformSLWitness, Matrix.mul_apply, finset_sum_coeff, coeff_C_mul,
    coeff_add, coeff_X_pow, Fintype.sum_prod_type, Fin.sum_univ_succ,
    mul_add, mul_ite, Finset.sum_add_distrib, polynomial_coeff_ite, hjp]

theorem uniformSLWitness_constant_matrix_obstruction (p q : r) (hpq : p ≠ q)
    (E : Matrix r (Fin 4 × r) K) (c : K[X])
    (hrel : E.map Polynomial.C * uniformSLWitness p q =
      (-c) • (1 : Matrix r r K[X])) : E = 0 ∧ c = 0 := by
  have hcoeff (d : ℕ) (i j : r) :
      ((E.map Polynomial.C * uniformSLWitness (K := K) p q) i j).coeff d =
        if i = j then -(c.coeff d) else 0 := by
    have h := congrArg (fun A : Matrix r r K[X] => (A i j).coeff d) hrel
    simpa [Matrix.smul_apply, Matrix.one_apply, mul_ite, polynomial_coeff_ite] using h
  have hlow (l : Fin 4) (i j : r) :
      E i (l, j) = if i = j then -(c.coeff l.val) else 0 := by
    rw [← uniformSLWitness_mul_coeff_low p q E l i j]
    exact hcoeff l.val i j
  have hfour (i j : r) :
      (if j = p then E i (0, p) else 0) +
      (if j = q then E i (1, p) else 0) +
      (if j = p then E i (2, q) else 0) =
        if i = j then -(c.coeff 4) else 0 := by
    rw [← uniformSLWitness_mul_coeff_four p q hpq E i j]
    exact hcoeff 4 i j
  have hfive (i j : r) :
      (if j = p then E i (3, p) else 0) = if i = j then -(c.coeff 5) else 0 := by
    rw [← uniformSLWitness_mul_coeff_five p q E i j]
    exact hcoeff 5 i j
  have hc4 : c.coeff 4 = 0 := by
    simpa [hlow, hpq, Ne.symm hpq] using (hfour q q).symm
  have hc0 : c.coeff 0 = 0 := by
    simpa [hlow, hpq, Ne.symm hpq, hc4] using hfour p p
  have hc1 : c.coeff 1 = 0 := by
    simpa [hlow, hpq, Ne.symm hpq] using hfour p q
  have hc2 : c.coeff 2 = 0 := by
    simpa [hlow, hpq, Ne.symm hpq] using hfour q p
  have hc5 : c.coeff 5 = 0 := by
    simpa [hlow, hpq, Ne.symm hpq] using (hfive q q).symm
  have hc3 : c.coeff 3 = 0 := by
    simpa [hlow, hc5] using hfive p p
  have hE : E = 0 := by
    funext i x
    rcases x with ⟨l, j⟩
    rw [hlow]
    fin_cases l <;> simp [hc0, hc1, hc2, hc3]
  refine ⟨hE, ?_⟩
  have h := congrArg (fun A : Matrix r r K[X] => A p p) hrel
  simpa [hE] using h.symm

/-- The scalar equation has no nonzero solution whose entries are constant. -/
theorem uniformSLWitness_constant_scalar_obstruction (p q : r) (hpq : p ≠ q)
    (E : Matrix r (Fin 4 × r) K[X]) (c : K[X]) (hE : DegreeBound E 0)
    (hrel : E * uniformSLWitness p q = (-c) • (1 : Matrix r r K[X])) :
    E = 0 ∧ c = 0 := by
  let E₀ : Matrix r (Fin 4 × r) K := fun i j => (E i j).coeff 0
  have he : E = E₀.map Polynomial.C := by
    funext i j
    exact eq_C_of_natDegree_le_zero (hE i j)
  obtain ⟨hz, hc⟩ := uniformSLWitness_constant_matrix_obstruction p q hpq E₀ c (by
    rwa [← he])
  refine ⟨?_, hc⟩
  rw [he, hz]
  simp

end FD56


