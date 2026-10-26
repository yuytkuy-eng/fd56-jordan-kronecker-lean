/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.SeparableDeterminant
import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
import Mathlib.RingTheory.Localization.FractionRing

/-! The characteristic polynomial of a matrix of independent variables is separable. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

theorem diagonal_charpoly (v : n → K) :
    (Matrix.diagonal v).charpoly = ∏ i, (X - C (v i)) := by
  have h : (Matrix.diagonal v).charmatrix = Matrix.diagonal (fun i => X-C (v i)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [Matrix.charmatrix_apply_ne, hij]
  rw [Matrix.charpoly,h,Matrix.det_diagonal]

theorem universal_matrix_charpoly_separable {F : Type*} [Field F]
    (ψ : MvPolynomial (n × n) K →+* F) (hψ : Function.Injective ψ) :
    ((Matrix.mvPolynomialX n n K).map ψ).charpoly.Separable := by
  let L := FractionRing (MvPolynomial n K)
  let ι : MvPolynomial n K →+* L := algebraMap _ _
  let ev : n → L := fun i => ι (MvPolynomial.X i)
  have hev : Function.Injective ev :=
    (IsFractionRing.injective (MvPolynomial n K) L).comp MvPolynomial.X_injective
  let φ : MvPolynomial (n × n) K →+* L :=
    MvPolynomial.eval₂Hom (ι.comp MvPolynomial.C) (fun ij => (Matrix.diagonal ev) ij.1 ij.2)
  have he : ((Matrix.mvPolynomialX n n K).map φ) = Matrix.diagonal ev := by
    ext i j
    simp [Matrix.mvPolynomialX,φ]
  rw [Matrix.charpoly_map]
  apply monic_separable_of_specialization _ (Matrix.charpoly_monic _) φ ψ hψ
  rw [← Matrix.charpoly_map,he,diagonal_charpoly]
  exact Polynomial.separable_prod_X_sub_C_iff.mpr hev

theorem generic_matrix_charpoly_separable :
    ((Matrix.mvPolynomialX n n K).map
      (algebraMap (MvPolynomial (n × n) K) (FractionRing (MvPolynomial (n × n) K)))).charpoly.Separable :=
  universal_matrix_charpoly_separable _ (IsFractionRing.injective _ _)

end FD56
