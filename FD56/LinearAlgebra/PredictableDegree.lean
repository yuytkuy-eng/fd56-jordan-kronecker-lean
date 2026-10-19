/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PolynomialMatrix

/-! Highest coefficients control weighted polynomial combinations.
The hypotheses concern actual column degree bounds and their leading matrix. -/

namespace FD56
open Polynomial Matrix
open scoped BigOperators
variable {K b k : Type*} [Field K] [Fintype k]

theorem polynomial_combination_coefficient (Z : Matrix b k K[X])
    (e : k → ℕ) (c : k → K[X]) (d : ℕ)
    (hZ : ∀ i j, (Z i j).natDegree ≤ e j)
    (hc : ∀ j, c j = 0 ∨ (e j ≤ d ∧ (c j).natDegree ≤ d - e j)) :
    ∀ i, ((Z *ᵥ c) i).coeff d =
      ∑ j, (Z i j).coeff (e j) * (c j).coeff (d - e j) := by
  intro i
  simp only [Matrix.mulVec, dotProduct, Polynomial.finset_sum_coeff]
  apply Finset.sum_congr rfl
  intro j _
  rcases hc j with hz | ⟨hle, hdeg⟩
  · simp [hz]
  · have hd : e j + (d - e j) = d := by omega
    simpa only [hd] using Polynomial.coeff_mul_add_eq_of_natDegree_le (hZ i j) hdeg

theorem polynomial_combination_degree_bound (Z : Matrix b k K[X])
    (e : k → ℕ) (c : k → K[X]) (d : ℕ)
    (hZ : ∀ i j, (Z i j).natDegree ≤ e j)
    (hc : ∀ j, c j = 0 ∨ (e j ≤ d ∧ (c j).natDegree ≤ d - e j)) :
    ∀ i, ((Z *ᵥ c) i).natDegree ≤ d := by
  intro i
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  change (Z i j * c j).natDegree ≤ d
  rcases hc j with hz | ⟨hle, hdeg⟩
  · simp [hz]
  · have hm : ((Z i j) * c j).natDegree ≤ (Z i j).natDegree + (c j).natDegree :=
      Polynomial.natDegree_mul_le
    have hz := hZ i j
    omega

/-- An injective leading matrix prevents cancellation at the weighted top degree. -/
theorem predictable_degree (Z : Matrix b k K[X])
    (e : k → ℕ) (c : k → K[X]) (d : ℕ)
    (hZ : ∀ i j, (Z i j).natDegree ≤ e j)
    (hc : ∀ j, c j = 0 ∨ (e j ≤ d ∧ (c j).natDegree ≤ d - e j))
    (hlead : Function.Injective (Matrix.mulVec (fun i j => (Z i j).coeff (e j))))
    (htop : ∃ j, (c j).coeff (d - e j) ≠ 0) :
    (∀ i, ((Z *ᵥ c) i).natDegree ≤ d) ∧
      ∃ i, ((Z *ᵥ c) i).natDegree = d ∧ ((Z *ᵥ c) i).coeff d ≠ 0 := by
  have hbound := polynomial_combination_degree_bound Z e c d hZ hc
  refine ⟨hbound, ?_⟩
  have hex : ∃ i, ((Z *ᵥ c) i).coeff d ≠ 0 := by
    by_contra hn
    push_neg at hn
    have hv : (fun j => (c j).coeff (d - e j)) = 0 := by
      apply hlead
      ext i
      rw [Matrix.mulVec_zero]
      exact (polynomial_combination_coefficient Z e c d hZ hc i).symm.trans (hn i)
    obtain ⟨j, hj⟩ := htop
    exact hj (congrArg (fun v => v j) hv)
  obtain ⟨i, hi⟩ := hex
  exact ⟨i, le_antisymm (hbound i) (Polynomial.le_natDegree_of_ne_zero hi), hi⟩

/-- Maximum weighted degree among nonzero coefficient polynomials. -/
noncomputable def weightedDegree (e : k → ℕ) (c : k → K[X]) : ℕ := by
  classical
  exact (Finset.univ.filter (fun j => c j ≠ 0)).sup (fun j => (c j).natDegree + e j)

theorem predictable_weighted_degree (Z : Matrix b k K[X])
    (e : k → ℕ) (c : k → K[X])
    (hZ : ∀ i j, (Z i j).natDegree ≤ e j)
    (hlead : Function.Injective (Matrix.mulVec (fun i j => (Z i j).coeff (e j))))
    (hc : c ≠ 0) :
    (∀ i, ((Z *ᵥ c) i).natDegree ≤ weightedDegree e c) ∧
      ∃ i, ((Z *ᵥ c) i).natDegree = weightedDegree e c ∧ (Z *ᵥ c) i ≠ 0 := by
  classical
  have hbounds : ∀ j, c j = 0 ∨
      (e j ≤ weightedDegree e c ∧ (c j).natDegree ≤ weightedDegree e c - e j) := by
    intro j
    by_cases hz : c j = 0
    · exact Or.inl hz
    · have hj : j ∈ Finset.univ.filter (fun j => c j ≠ 0) := by simp [hz]
      have hle := Finset.le_sup (f := fun j => (c j).natDegree + e j) hj
      change (c j).natDegree + e j ≤ weightedDegree e c at hle
      exact Or.inr ⟨by omega, by omega⟩
  have hnonempty : (Finset.univ.filter (fun j => c j ≠ 0)).Nonempty := by
    by_contra hn
    apply hc
    apply _root_.funext
    intro j
    change c j = 0
    by_contra hj
    exact hn ⟨j, by simp [hj]⟩
  obtain ⟨j, hj, hd⟩ := Finset.exists_mem_eq_sup _ hnonempty (fun j => (c j).natDegree + e j)
  change weightedDegree e c = (c j).natDegree + e j at hd
  have hj0 : c j ≠ 0 := (Finset.mem_filter.mp hj).2
  have htop : ∃ j, (c j).coeff (weightedDegree e c - e j) ≠ 0 := by
    refine ⟨j, ?_⟩
    rw [hd, Nat.add_sub_cancel, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hj0
  obtain ⟨hb, i, hi, hcoeff⟩ := predictable_degree Z e c (weightedDegree e c) hZ hbounds hlead htop
  refine ⟨hb, i, hi, ?_⟩
  intro hz
  exact hcoeff (by rw [hz]; simp)

/-- The degree filtration of a reduced polynomial basis is exactly the
weighted coordinate filtration, including coefficients forced to vanish. -/
theorem polynomial_combination_degree_iff (Z : Matrix b k K[X])
    (e : k → ℕ) (c : k → K[X]) (d : ℕ)
    (hZ : ∀ i j, (Z i j).natDegree ≤ e j)
    (hlead : Function.Injective (Matrix.mulVec (fun i j => (Z i j).coeff (e j)))) :
    (∀ i, ((Z *ᵥ c) i).natDegree ≤ d) ↔
      ∀ j, c j = 0 ∨ (e j ≤ d ∧ (c j).natDegree ≤ d - e j) := by
  classical
  constructor
  · intro hout j
    by_cases hz : c j = 0
    · exact Or.inl hz
    · have hc : c ≠ 0 := by intro hc; apply hz; exact congrArg (fun v => v j) hc
      obtain ⟨_, i, hi, _⟩ := predictable_weighted_degree Z e c hZ hlead hc
      have hd : weightedDegree e c ≤ d := hi ▸ hout i
      have hj : j ∈ Finset.univ.filter (fun j => c j ≠ 0) := by simp [hz]
      have hle := Finset.le_sup (f := fun j => (c j).natDegree + e j) hj
      change (c j).natDegree + e j ≤ weightedDegree e c at hle
      exact Or.inr ⟨by omega, by omega⟩
  · exact polynomial_combination_degree_bound Z e c d hZ

end FD56
