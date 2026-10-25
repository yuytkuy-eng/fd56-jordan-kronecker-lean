/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.NonconstantCoordinate
import FD56.LinearAlgebra.PolynomialHypersurface
import FD56.LinearAlgebra.FiniteFieldGenerators
import Mathlib.Algebra.Polynomial.AlgebraMap

/-! Independent coordinates and generator bounds for a nonconstant principal kernel. -/

noncomputable section
namespace FD56

variable {K F σ : Type*} [Field K] [Field F] [Algebra K F]

theorem remaining_coordinates_independent_of_principal_kernel_at
    (φ : MvPolynomial σ K →ₐ[K] F) (g : MvPolynomial σ K) (i : σ)
    (hi : 0 < (coordinatePolynomialEquiv i g).natDegree)
    (hker : ∀ p, φ p = 0 ↔ g ∣ p) :
    AlgebraicIndependent K (fun j : {j : σ // j ≠ i} => φ (MvPolynomial.X j.val)) := by
  let e := coordinatePolynomialEquiv (R := K) i
  let f : MvPolynomial {j : σ // j ≠ i} K →ₐ[K] F :=
    (φ.comp e.symm.toAlgHom).comp Polynomial.CAlgHom
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have hd : e g ∣ Polynomial.C a := by
      have hd' := (hker (e.symm (Polynomial.C a))).mp ha
      simpa only [AlgEquiv.apply_symm_apply] using map_dvd e hd'
    by_contra hn
    have hdg := Polynomial.natDegree_le_of_dvd hd
      (show Polynomial.C a ≠ 0 by simpa using hn)
    have hz : (e g).natDegree = 0 := Nat.eq_zero_of_le_zero (by simpa using hdg)
    exact (Nat.ne_of_gt hi) hz
  have hai := (MvPolynomial.algebraicIndependent_X {j : σ // j ≠ i} K).map' (f := f) hf
  have he (j : {j : σ // j ≠ i}) : e.symm (Polynomial.C (MvPolynomial.X j)) =
      MvPolynomial.X j.val := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (coordinatePolynomialEquiv_other i j).symm
  have hfun : (f ∘ MvPolynomial.X) =
      (fun j : {j : σ // j ≠ i} => φ (MvPolynomial.X j.val)) := by
    funext j
    change φ (e.symm (Polynomial.C (MvPolynomial.X j))) = _
    rw [he]
  rw [hfun] at hai
  exact hai

theorem exists_remaining_coordinates_independent_of_principal_kernel
    (φ : MvPolynomial σ K →ₐ[K] F) (g : MvPolynomial σ K)
    (hg : g ≠ 0) (hu : ¬IsUnit g) (hker : ∀ p, φ p = 0 ↔ g ∣ p) :
    ∃ i : σ, AlgebraicIndependent K
      (fun j : {j : σ // j ≠ i} => φ (MvPolynomial.X j.val)) := by
  obtain ⟨i, hi⟩ := exists_positive_degree_coordinate_equiv g hg hu
  exact ⟨i, remaining_coordinates_independent_of_principal_kernel_at φ g i hi hker⟩

theorem card_sub_one_le_card_of_principal_kernel_field_generators
    [Fintype σ] {ι : Type*} [Fintype ι]
    (φ : MvPolynomial σ K →ₐ[K] F) (g : MvPolynomial σ K)
    (hg : g ≠ 0) (hu : ¬IsUnit g) (hker : ∀ p, φ p = 0 ↔ g ∣ p)
    (y : ι → F) (hy : IntermediateField.adjoin K (Set.range y) = ⊤) :
    Fintype.card σ - 1 ≤ Fintype.card ι := by
  classical
  obtain ⟨i, hi⟩ := exists_remaining_coordinates_independent_of_principal_kernel φ g hg hu hker
  have hc := card_le_card_of_algebraicIndependent_of_finite_field_generators hi y hy
  simpa only [ne_eq, Fintype.card_subtype_compl, Fintype.card_subtype_eq] using hc

end FD56
