/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.WeightedRowLifting
import FD56.Hilbert.MinimalProfile
import FD56.Hilbert.EventualHilbertBudget

/-! The total kernel degree of a primitive row-reduced polynomial matrix.
This budget does not require the individual minimal degrees to be balanced. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K m n : Type*} [Field K] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

theorem polynomial_kernel_eventual_row_budget
    (A : Matrix m n K[X]) (R : Matrix n m K[X]) (hAR : A*R=1)
    (e : m → ℕ) (hA : ∀ i j, (A i j).natDegree≤e i)
    (hlead : Function.Surjective (show Matrix m n K from fun i j => (A i j).coeff (e i)).mulVec) :
    ∃ N : ℕ, ∀ d, N≤d →
      Module.finrank K (polynomialKernelAtDegree A d)+Fintype.card m*(d+1)+(∑ i, e i)=
        Fintype.card n*(d+1) := by
  obtain ⟨N,hN⟩ := weighted_row_coefficient_surjective_eventually A R hAR e hA hlead
  refine ⟨N,?_⟩
  intro d hd
  let F := weightedCoefficientMatrix A (fun _ => d) (fun i => d+e i)
  have hs : Function.Surjective (Matrix.toLin' F) := hN d hd
  have hh := (Matrix.toLin' F).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs,finrank_top] at hh
  have hk : Module.finrank K (LinearMap.ker (Matrix.toLin' F))=
      Module.finrank K (polynomialKernelAtDegree A d) :=
    weighted_coefficient_kernel_finrank A (fun _ => d) (fun i => d+e i)
      (by intro i j; change (A i j).natDegree+d≤d+e i; have := hA i j; omega)
  rw [hk] at hh
  simp only [Module.finrank_fintype_fun_eq_card,Fintype.card_sigma,Fintype.card_fin,
    Finset.sum_const,Finset.card_univ,smul_eq_mul] at hh
  have hout : (∑ i : m, (d+e i+1))=Fintype.card m*(d+1)+(∑ i, e i) := by
    simp_rw [show ∀ i, d+e i+1=(d+1)+e i by intro i; omega]
    rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    rfl
  rw [hout] at hh
  omega

theorem minimal_degree_budget_of_right_inverse_and_leading
    (A : Matrix m n K[X]) (R : Matrix n m K[X]) (hAR : A*R=1)
    (e : m → ℕ) (hA : ∀ i j, (A i j).natDegree≤e i)
    (hlead : Function.Surjective (show Matrix m n K from fun i j => (A i j).coeff (e i)).mulVec)
    (xs : List ℕ) (hmin : HasMinimalKernelDegrees A xs) :
    xs.length+Fintype.card m=Fintype.card n ∧ xs.sum=∑ i, e i := by
  obtain ⟨N,hN⟩ := polynomial_kernel_eventual_row_budget A R hAR e hA hlead
  let d := N+xs.sum
  have h0 := hN d (by dsimp [d]; omega)
  have h1 := hN (d+1) (by dsimp [d]; omega)
  rw [(hasMinimalKernelDegrees_iff_hilbert _ _).mp hmin] at h0 h1
  have hx0 := degreeList_hilbert_add_sum xs d (by dsimp [d]; omega)
  have hx1 := degreeList_hilbert_add_sum xs (d+1) (by dsimp [d]; omega)
  have hl : xs.length+Fintype.card m=Fintype.card n := by nlinarith
  refine ⟨hl,?_⟩
  rw [← hl,Nat.add_mul] at h0
  omega

end FD56
