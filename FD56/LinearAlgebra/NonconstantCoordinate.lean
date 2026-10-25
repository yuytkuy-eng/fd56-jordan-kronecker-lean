/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Logic.Equiv.Option

/-! A nonconstant multivariate polynomial has a coordinate of positive degree. -/

namespace FD56
open MvPolynomial
variable {R K σ : Type*} [CommSemiring R] [Field K]

theorem exists_positive_degree_of_not_constant (p : MvPolynomial σ R)
    (h : p ≠ C (p.coeff 0)) : ∃ i, 0 < p.degreeOf i := by
  classical
  by_contra hn
  have hz : ∀ i, p.degreeOf i = 0 := by simpa using hn
  have hs : ∀ d ∈ p.support, d = 0 := by
    intro d hd
    apply Finsupp.ext
    intro i
    exact Nat.eq_zero_of_le_zero ((degreeOf_le_iff.mp (le_of_eq (hz i))) d hd)
  have ht : p.totalDegree = 0 := Nat.eq_zero_of_le_zero (by
    rw [totalDegree, Finset.sup_le_iff]
    intro d hd
    rw [hs d hd]
    simp)
  exact h (totalDegree_eq_zero_iff_eq_C.mp ht)

theorem exists_positive_degree_of_nonzero_nonunit (p : MvPolynomial σ K)
    (hp : p ≠ 0) (hu : ¬IsUnit p) : ∃ i, 0 < p.degreeOf i := by
  apply exists_positive_degree_of_not_constant p
  intro hc
  have hz : p.coeff 0 ≠ 0 := by
    intro hz
    apply hp
    rw [hc, hz, map_zero]
  apply hu
  rw [hc]
  exact (isUnit_iff_ne_zero.mpr hz).map C

noncomputable def coordinatePolynomialEquiv (i : σ) :
    MvPolynomial σ R ≃ₐ[R] Polynomial (MvPolynomial {j : σ // j ≠ i} R) := by
  classical
  exact (renameEquiv R (Equiv.optionSubtypeNe i).symm).trans
    (optionEquivLeft R {j : σ // j ≠ i})

theorem coordinatePolynomialEquiv_natDegree (i : σ) (p : MvPolynomial σ R) :
    (coordinatePolynomialEquiv i p).natDegree = p.degreeOf i := by
  classical
  change (optionEquivLeft R {j : σ // j ≠ i}
    (rename (Equiv.optionSubtypeNe i).symm p)).natDegree = _
  rw [natDegree_optionEquivLeft]
  have hh := degreeOf_rename_of_injective (p := p) (Equiv.optionSubtypeNe i).symm.injective i
  simpa only [Equiv.optionSubtypeNe_symm_self] using hh

theorem coordinatePolynomialEquiv_self (i : σ) :
    coordinatePolynomialEquiv (R := R) i (X i) = Polynomial.X := by
  classical
  simp [coordinatePolynomialEquiv, Equiv.optionSubtypeNe_symm_self, optionEquivLeft_X_none]

theorem coordinatePolynomialEquiv_other (i : σ) (j : {j : σ // j ≠ i}) :
    coordinatePolynomialEquiv (R := R) i (X j.val) = Polynomial.C (X j) := by
  classical
  simp [coordinatePolynomialEquiv, Equiv.optionSubtypeNe_symm_of_ne j.property,
    optionEquivLeft_X_some]

theorem exists_positive_degree_coordinate_equiv (p : MvPolynomial σ K)
    (hp : p ≠ 0) (hu : ¬IsUnit p) :
    ∃ i, 0 < (coordinatePolynomialEquiv i p).natDegree := by
  obtain ⟨i, hi⟩ := exists_positive_degree_of_nonzero_nonunit p hp hu
  exact ⟨i, by simpa only [coordinatePolynomialEquiv_natDegree] using hi⟩

end FD56
