/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.FamilySLWitness
import FD56.Hilbert.KernelDimension

/-! The two lowest relevant truncations of the sparse family witness. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K : Type*} [Field K]

private theorem polynomial_degree_two_eq_zero (p : K[X]) (hp : p.natDegree ≤ 2)
    (h0 : p.coeff 0 = 0) (h1 : p.coeff 1 = 0) (h2 : p.coeff 2 = 0) : p = 0 := by
  apply Polynomial.ext
  intro k
  by_cases hk : k ≤ 2
  · interval_cases k <;> simpa using ‹p.coeff _ = 0›
  · simpa using coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp (by omega))

/-- Every quadratic left-kernel vector is a constant multiple of the last
two-coordinate relation. -/
theorem familySLWitness_quadratic_kernel
    (e : Fin 8 → K[X]) (he : ∀ i, (e i).natDegree ≤ 2)
    (hker : (familySLWitness (K := K)).transpose *ᵥ e = 0) :
    e = ![0, 0, 0, 0, 0, 0, -C ((e 7).coeff 0) * X ^ 2, C ((e 7).coeff 0)] := by
  have hc (i : Fin 8) (k : ℕ) (hk : 2 < k) : (e i).coeff k = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (he i) hk)
  have hA : e 0 + e 1 * X ^ 3 + e 2 * X ^ 5 = 0 := by
    have h := congrFun hker (0 : Fin 3)
    simpa [familySLWitness, Matrix.transpose_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, mul_comm, add_assoc] using h
  have hB : e 1 * X ^ 2 + e 2 + e 3 * X + e 4 * X ^ 4 + e 5 * X ^ 5 = 0 := by
    have h := congrFun hker (1 : Fin 3)
    simpa [familySLWitness, Matrix.transpose_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, mul_comm, add_assoc] using h
  have hC : e 0 + e 5 + e 6 * X ^ 2 + e 7 * X ^ 4 = 0 := by
    have h := congrFun hker (2 : Fin 3)
    simpa [familySLWitness, Matrix.transpose_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, mul_comm, add_assoc] using h
  have hz0 : e 0 = 0 := by
    apply polynomial_degree_two_eq_zero _ (he 0)
    · simpa [coeff_mul_X_pow'] using congrArg (fun p : K[X] => p.coeff 0) hA
    · simpa [coeff_mul_X_pow'] using congrArg (fun p : K[X] => p.coeff 1) hA
    · simpa [coeff_mul_X_pow'] using congrArg (fun p : K[X] => p.coeff 2) hA
  have hz2 : e 2 = 0 := by
    apply polynomial_degree_two_eq_zero _ (he 2)
    · simpa [coeff_mul_X_pow', coeff_mul_X_zero] using
        congrArg (fun p : K[X] => p.coeff 0) hB
    · simpa [coeff_mul_X_pow', hc] using congrArg (fun p : K[X] => p.coeff 6) hA
    · simpa [coeff_mul_X_pow', hc] using congrArg (fun p : K[X] => p.coeff 7) hA
  have hz1 : e 1 = 0 := by
    apply polynomial_degree_two_eq_zero _ (he 1)
    · simpa [coeff_mul_X_pow', hz0] using congrArg (fun p : K[X] => p.coeff 3) hA
    · simpa [coeff_mul_X_pow', hz0] using congrArg (fun p : K[X] => p.coeff 4) hA
    · simpa [coeff_mul_X_pow', hz0, hz2] using congrArg (fun p : K[X] => p.coeff 5) hA
  have hz3 : e 3 = 0 := by
    apply polynomial_degree_two_eq_zero _ (he 3)
    · simpa [coeff_mul_X_pow', coeff_mul_X, hz1, hz2] using
        congrArg (fun p : K[X] => p.coeff 1) hB
    · simpa [coeff_mul_X_pow', coeff_mul_X, hz1, hz2] using
        congrArg (fun p : K[X] => p.coeff 2) hB
    · simpa [coeff_mul_X_pow', coeff_mul_X, hz1, hz2] using
        congrArg (fun p : K[X] => p.coeff 3) hB
  have hz5 : e 5 = 0 := by
    apply polynomial_degree_two_eq_zero _ (he 5)
    · simpa [coeff_mul_X_pow', hz0] using congrArg (fun p : K[X] => p.coeff 0) hC
    · simpa [coeff_mul_X_pow', hz0] using congrArg (fun p : K[X] => p.coeff 1) hC
    · simpa [coeff_mul_X_pow', coeff_mul_X, hc] using
        congrArg (fun p : K[X] => p.coeff 7) hB
  have hz4 : e 4 = 0 := by
    apply polynomial_degree_two_eq_zero _ (he 4)
    · simpa [coeff_mul_X_pow', coeff_mul_X, hz1, hz2, hz3, hz5] using
        congrArg (fun p : K[X] => p.coeff 4) hB
    · simpa [coeff_mul_X_pow', coeff_mul_X, hz1, hz2, hz3, hz5] using
        congrArg (fun p : K[X] => p.coeff 5) hB
    · simpa [coeff_mul_X_pow', coeff_mul_X, hz1, hz2, hz3, hz5] using
        congrArg (fun p : K[X] => p.coeff 6) hB
  have ha6 : (e 6).coeff 0 = 0 := by
    simpa [coeff_mul_X_pow', hz0, hz5] using congrArg (fun p : K[X] => p.coeff 2) hC
  have hb6 : (e 6).coeff 1 = 0 := by
    simpa [coeff_mul_X_pow', hz0, hz5] using congrArg (fun p : K[X] => p.coeff 3) hC
  have hc6 : (e 6).coeff 2 = -(e 7).coeff 0 := by
    have h : (e 6).coeff 2 + (e 7).coeff 0 = 0 := by
      simpa [coeff_mul_X_pow', hz0, hz5] using congrArg (fun p : K[X] => p.coeff 4) hC
    exact eq_neg_of_add_eq_zero_left h
  have hb7 : (e 7).coeff 1 = 0 := by
    simpa [coeff_mul_X_pow', hc] using congrArg (fun p : K[X] => p.coeff 5) hC
  have hc7 : (e 7).coeff 2 = 0 := by
    simpa [coeff_mul_X_pow', hc] using congrArg (fun p : K[X] => p.coeff 6) hC
  have hz6 : e 6 = -C ((e 7).coeff 0) * X ^ 2 := by
    apply Polynomial.ext
    intro k
    by_cases hk : k ≤ 2
    · interval_cases k <;> simp [coeff_mul_X_pow', ha6, hb6, hc6]
    · have hk' : 2 < k := by omega
      have hk0 : k - 2 ≠ 0 := by omega
      simp [coeff_mul_X_pow', hc _ _ hk', coeff_C, hk0]
  have hz7 : e 7 = C ((e 7).coeff 0) := by
    apply Polynomial.ext
    intro k
    by_cases hk : k ≤ 2
    · interval_cases k <;> simp [hb7, hc7]
    · have hk' : 2 < k := by omega
      have hk0 : k ≠ 0 := by omega
      simp [hc _ _ hk', coeff_C, hk0]
  funext i
  fin_cases i
  · simpa using hz0
  · simpa using hz1
  · simpa using hz2
  · simpa using hz3
  · simpa using hz4
  · simpa using hz5
  · simpa only [Matrix.cons_val_succ, Matrix.cons_val_zero, neg_mul] using hz6
  · simpa using hz7

/-- An affine left-kernel vector of the sparse witness is zero. -/
theorem familySLWitness_affine_kernel_zero
    (e : Fin 8 → K[X]) (he : ∀ i, (e i).natDegree ≤ 1)
    (hker : (familySLWitness (K := K)).transpose *ᵥ e = 0) : e = 0 := by
  have hh := familySLWitness_quadratic_kernel e (fun i => (he i).trans (by decide)) hker
  have ha : (e 7).coeff 0 = 0 := by
    have h := congrArg (fun p : K[X] => p.coeff 2) (congrFun hh 6)
    have hz : (e 6).coeff 2 = 0 := coeff_eq_zero_of_natDegree_lt (by have := he 6; omega)
    simpa [coeff_mul_X_pow', hz] using h.symm
  rw [hh]
  simp only [ha, C_0, neg_zero, zero_mul]
  funext i
  fin_cases i <;> rfl

private def familySLQuadraticVector (t : K) : Fin 8 → K[X] :=
  ![0, 0, 0, 0, 0, 0, -C t * X ^ 2, C t]

private theorem familySLQuadraticVector_degree (t : K) (i : Fin 8) :
    (familySLQuadraticVector t i).natDegree ≤ 2 := by
  fin_cases i <;> simp [familySLQuadraticVector]
  exact natDegree_C_mul_X_pow_le t 2

private theorem familySLQuadraticVector_kernel (t : K) :
    (familySLWitness (K := K)).transpose *ᵥ familySLQuadraticVector t = 0 := by
  funext j
  fin_cases j <;>
    simp [familySLWitness, familySLQuadraticVector, Matrix.transpose_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

/-- The quadratic bounded kernel has exactly one constant parameter. -/
def familySLWitnessQuadraticKernelEquiv :
    polynomialKernelAtDegree (familySLWitness (K := K)).transpose 2 ≃ₗ[K] K where
  toFun e := ((e.val 7).val).coeff 0
  invFun t := ⟨fun i => boundedPolyOf (familySLQuadraticVector t i)
    (familySLQuadraticVector_degree t i), familySLQuadraticVector_kernel t⟩
  left_inv e := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    exact (congrFun (familySLWitness_quadratic_kernel (fun j => (e.val j).val)
      (fun j => boundedPoly_degree 2 (e.val j)) e.property) i).symm
  right_inv t := by simp [familySLQuadraticVector, boundedPolyOf]
  map_add' e f := by simp
  map_smul' t e := by simp

theorem familySLWitness_quadratic_kernel_finrank :
    Module.finrank K (polynomialKernelAtDegree (familySLWitness (K := K)).transpose 2) = 1 := by
  rw [familySLWitnessQuadraticKernelEquiv.finrank_eq]
  exact Module.finrank_self K

theorem familySLWitness_affine_kernel_eq_bot :
    polynomialKernelAtDegree (familySLWitness (K := K)).transpose 1 = ⊥ := by
  apply le_antisymm
  · intro e he
    have hh := familySLWitness_affine_kernel_zero (fun j => (e j).val)
      (fun j => boundedPoly_degree 1 (e j)) he
    change e = 0
    funext i
    apply Subtype.ext
    exact congrFun hh i
  · exact bot_le

theorem familySLWitness_affine_kernel_finrank :
    Module.finrank K (polynomialKernelAtDegree (familySLWitness (K := K)).transpose 1) = 0 := by
  rw [familySLWitness_affine_kernel_eq_bot, finrank_bot]

end FD56

