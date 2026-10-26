/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.ObservabilityScalarAdjugate
import FD56.LinearAlgebra.WeightedDeterminantDegree
import FD56.LinearAlgebra.PolynomialLeading

/-! Row-weighted degrees of the explicit observability scalar solutions. -/

namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem polynomial_adjugate_natDegree_add_row_bound (A : Matrix n n K[X])
    (w : n → ℕ) (hA : ∀ i j, (A i j).natDegree ≤ w i) (i j : n) :
    (A.adjugate i j).natDegree+w j ≤ ∑ k, w k := by
  rw [Matrix.adjugate_apply]
  have hrow : ∀ a b, ((A.updateRow j (Pi.single i 1)) a b).natDegree ≤
      if a=j then 0 else w a := by
    intro a b
    by_cases ha : a=j
    · subst a
      by_cases hb : b=i <;> simp [Matrix.updateRow_apply,Pi.single_apply,hb]
    · simpa [Matrix.updateRow_apply,ha] using hA a b
  have hd := polynomial_det_natDegree_le_row_sum _ _ hrow
  have hs : (∑ k, if k=j then 0 else w k)+w j=∑ k, w k := by
    have he : w j=∑ k, if k=j then w k else 0 := by simp
    conv_lhs => rw [he]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    by_cases h : k=j <;> simp [h]
  omega

theorem observability_adjugate_solution_degree (M : Matrix n n K[X])
    (P : Matrix m n K[X]) (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (level : n → ℕ) (row : n → m) (e : ℕ)
    (he : (∑ k, (level k+1))=e+1) :
    let C := observabilitySelectedMatrix M P level row
    DegreeBound (observabilityScalarX M P C.adjugate level row) e ∧
      DegreeBound (observabilityScalarU M C.adjugate level row) e ∧
      C.det.natDegree ≤ e+1 := by
  dsimp only
  let C := observabilitySelectedMatrix M P level row
  have hpow (i : ℕ) : DegreeBound (M^i) i := by
    simpa using degreeBound_pow M 1 hM i
  have hC : ∀ i j, (C i j).natDegree ≤ level i+1 := by
    intro i j
    exact (degreeBound_mul hP (hpow (level i)) (row i) j).trans (by omega)
  have hl (k : n) : level k ≤ e := by
    have h := Finset.single_le_sum (fun j _ => Nat.zero_le (level j+1)) (Finset.mem_univ k)
    rw [he] at h
    omega
  have hN (i k : n) : (C.adjugate i k).natDegree ≤ e-level k := by
    have h := polynomial_adjugate_natDegree_add_row_bound C (fun k => level k+1) hC i k
    rw [he] at h
    omega
  have hE (k : n) : DegreeBound (observabilityScalarColumn C.adjugate row k) (e-level k) := by
    intro i a
    dsimp only [observabilityScalarColumn]
    split_ifs
    · exact hN i k
    · simp
  refine ⟨?_,?_,?_⟩
  · intro i j
    simp only [observabilityScalarX,Matrix.sum_apply,matrixCommutatorSum]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro k _
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro s hs
    have hsi : s < level k := Finset.mem_range.mp hs
    have hd := degreeBound_mul (degreeBound_mul (hpow s) (degreeBound_mul (hE k) hP))
      (hpow (level k-1-s)) i j
    exact hd.trans (by have hh := hl k; omega)
  · intro i a
    simp only [observabilityScalarU,Matrix.sum_apply]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro k _
    exact (degreeBound_mul (hpow (level k)) (hE k) i a).trans (by have hh := hl k; omega)
  · have hd := polynomial_det_natDegree_le_row_sum C (fun k => level k+1) hC
    rwa [he] at hd

end FD56
