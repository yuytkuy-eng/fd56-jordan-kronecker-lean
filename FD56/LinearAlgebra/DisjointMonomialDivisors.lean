/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.DisjointVariableDivisors

/-! Products of variables with disjoint index sets have only unit common divisors. -/

namespace FD56
open scoped BigOperators
variable {K σ ι κ : Type*} [Field K] [Fintype ι] [Fintype κ]

theorem variable_product_degreeOf_zero (a : ι → σ) (s : σ) (ha : ∀ i, a i ≠ s) :
    (∏ i, (MvPolynomial.X (a i) : MvPolynomial σ K)).degreeOf s = 0 := by
  classical
  apply Nat.eq_zero_of_le_zero
  apply (MvPolynomial.degreeOf_prod_le s Finset.univ _).trans
  simp [MvPolynomial.degreeOf_X, fun i => Ne.symm (ha i)]

theorem disjoint_variable_products_common_divisor_isUnit (a : ι → σ) (b : κ → σ)
    (hab : ∀ i j, a i ≠ b j) (p : MvPolynomial σ K)
    (ha : p ∣ ∏ i, MvPolynomial.X (a i))
    (hb : p ∣ ∏ j, MvPolynomial.X (b j)) : IsUnit p := by
  classical
  let f : Bool → MvPolynomial σ K := fun c =>
    if c then ∏ i, MvPolynomial.X (a i) else ∏ j, MvPolynomial.X (b j)
  have hfn : ∀ c, f c ≠ 0 := by
    intro c
    cases c <;> simp [f,Finset.prod_ne_zero_iff,MvPolynomial.X_ne_zero]
  apply common_divisor_isUnit_of_variable_omissions f ⟨true,hfn true⟩ ?_ p ?_
  · intro s
    by_cases h : ∃ i, a i = s
    · obtain ⟨i,hi⟩ := h
      refine ⟨false,hfn false,?_⟩
      change (∏ j, (MvPolynomial.X (b j) : MvPolynomial σ K)).degreeOf s = 0
      apply variable_product_degreeOf_zero
      intro j hj
      exact hab i j (hi.trans hj.symm)
    · refine ⟨true,hfn true,?_⟩
      change (∏ i, (MvPolynomial.X (a i) : MvPolynomial σ K)).degreeOf s = 0
      apply variable_product_degreeOf_zero
      simpa using h
  · intro c
    cases c
    · exact hb
    · exact ha

end FD56
