/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PolynomialDerivationImage

/-! A maximal coefficient differential rank forces the column degrees of a
polynomial Plucker presentation to differ by at most one. -/

noncomputable section
namespace FD56
open Polynomial
open scoped BigOperators

variable {K L m r ι : Type*} [Field K] [Field L] [Algebra K L]
  [Fintype m] [Fintype r] [DecidableEq r]

omit [DecidableEq r] in
theorem degreeEndomorphismDimension_balanced_of_rank_budget
    (d : r → ℕ) (rank rows : ℕ) (hcard : Fintype.card r ≤ rows)
    (hlower : rows * (∑ j, d j) + (rows-Fintype.card r)*Fintype.card r+1 ≤ rank)
    (hupper : rank+degreeEndomorphismDimension d ≤
      1+rows*(∑ j, (d j+1))) :
    ∀ i j, d i ≤ d j+1 := by
  apply (degreeEndomorphismDimension_le_card_sq_iff d).mp
  have hsum : (∑ j, (d j+1))=(∑ j, d j)+Fintype.card r := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      mul_one]
  rw [hsum] at hupper
  have hc : rows=Fintype.card r+(rows-Fintype.card r) := by omega
  nlinarith

theorem polynomial_derivation_signed_plucker_degrees_balanced
    (row : ι → r → m) (sign : ι → K)
    (c : L) (G : Matrix m r L[X]) (d : r → ℕ)
    (hdegree : ∀ i j, (G i j).natDegree ≤ d j)
    (hG : Function.Injective G.mulVec)
    (hcard : Fintype.card r ≤ Fintype.card m)
    (hrank : Fintype.card m*(∑ j, d j)+
      (Fintype.card m-Fintype.card r)*Fintype.card r+1 ≤
      Module.finrank L (LinearMap.range (polynomialDerivationImageMap
        (fun i => C (algebraMap K L (sign i))*C c*pluckerMinorVector G (row i)) :
          Derivation K L L →ₗ[L] (ι → L[X])))) :
    ∀ i j, d i ≤ d j+1 := by
  exact degreeEndomorphismDimension_balanced_of_rank_budget d _ _ hcard hrank
    (polynomial_derivation_signed_selected_plucker_rank_bound row sign c G d hdegree hG)

theorem polynomial_derivation_selected_plucker_degrees_balanced
    (row : ι → r → m) (c : L) (G : Matrix m r L[X]) (d : r → ℕ)
    (hdegree : ∀ i j, (G i j).natDegree ≤ d j)
    (hG : Function.Injective G.mulVec)
    (hcard : Fintype.card r ≤ Fintype.card m)
    (hrank : Fintype.card m*(∑ j, d j)+
      (Fintype.card m-Fintype.card r)*Fintype.card r+1 ≤
      Module.finrank L (LinearMap.range (polynomialDerivationImageMap
        (fun i => C c*pluckerMinorVector G (row i)) :
          Derivation K L L →ₗ[L] (ι → L[X])))) :
    ∀ i j, d i ≤ d j+1 := by
  apply polynomial_derivation_signed_plucker_degrees_balanced (K:=K) row (fun _ => 1) c G d
    hdegree hG hcard
  have he : (fun i => C (algebraMap K L (1:K))*C c*pluckerMinorVector G (row i))=
      (fun i => C c*pluckerMinorVector G (row i)) := by
    funext i
    simp
  rw [he]
  exact hrank

end FD56
