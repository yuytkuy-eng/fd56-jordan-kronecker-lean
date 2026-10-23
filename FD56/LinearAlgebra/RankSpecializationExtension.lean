/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.RankSpecialization
import Mathlib.Algebra.MvPolynomial.CommRing

/-! Rank transfer from a specialization into an arbitrary field. Formal
inverse entries allow determinant transfer without a coefficient-ring section. -/

noncomputable section
namespace FD56
open Matrix
variable {R K F a b : Type*} [CommRing R] [Field K] [Field F]
  [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

theorem matrix_injective_of_field_specialization
    (ψ : R →+* K) (φ : R →+* F) (hφ : Function.Injective φ)
    (A : Matrix a b R) (hA : Function.Injective (A.map ψ).mulVec) :
    Function.Injective (A.map φ).mulVec := by
  classical
  obtain ⟨L, hL⟩ := matrix_left_inverse_of_injective (A.map ψ) hA
  let S := MvPolynomial (b × a) R
  let T := MvPolynomial (b × a) F
  let Q := FractionRing T
  let E : Matrix b a S := fun i j => MvPolynomial.X (i, j)
  let ψ' : S →+* K := MvPolynomial.eval₂Hom ψ (fun ij => L ij.1 ij.2)
  let φ' : S →+* Q := (algebraMap T Q).comp (MvPolynomial.map φ)
  have hφ' : Function.Injective φ' :=
    (IsFractionRing.injective T Q).comp (MvPolynomial.map_injective φ hφ)
  have hE : E.map ψ' = L := by
    ext i j
    exact MvPolynomial.eval₂Hom_X' _ _ _
  have hC : (A.map MvPolynomial.C).map ψ' = A.map ψ := by
    ext i j
    exact MvPolynomial.eval₂Hom_C _ _ _
  have hd : Matrix.det ((E * A.map MvPolynomial.C).map ψ') ≠ 0 := by
    rw [Matrix.map_mul, hE, hC, hL, Matrix.det_one]
    exact one_ne_zero
  have hd' := det_ne_zero_of_specialization ψ' φ' hφ'
    (E * A.map MvPolynomial.C) hd
  let ι : F →+* Q := (algebraMap T Q).comp MvPolynomial.C
  have hι : Function.Injective ι :=
    (IsFractionRing.injective T Q).comp (MvPolynomial.C_injective _ _)
  have hC' : (A.map MvPolynomial.C).map φ' = (A.map φ).map ι := by
    ext i j
    exact congrArg (algebraMap T Q) (MvPolynomial.map_C φ (A i j))
  rw [Matrix.map_mul, hC'] at hd'
  apply matrix_mulVec_injective_of_map ι hι
  let U := ((E.map φ') * ((A.map φ).map ι))⁻¹ * E.map φ'
  have hU : U * (A.map φ).map ι = 1 := by
    rw [Matrix.mul_assoc]
    exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hd')
  intro v w h
  have hh := congrArg (fun z => U *ᵥ z) h
  simpa only [Matrix.mulVec_mulVec, hU, Matrix.one_mulVec] using hh

theorem matrix_surjective_of_field_specialization
    (ψ : R →+* K) (φ : R →+* F) (hφ : Function.Injective φ)
    (A : Matrix a b R) (hA : Function.Surjective (A.map ψ).mulVec) :
    Function.Surjective (A.map φ).mulVec := by
  have hT := matrix_transpose_injective_of_surjective (A.map ψ) hA
  have hT' : Function.Injective ((A.transpose).map ψ).mulVec := hT
  have hF := matrix_injective_of_field_specialization ψ φ hφ A.transpose hT'
  obtain ⟨L, hL⟩ := matrix_left_inverse_of_injective (A.transpose.map φ) hF
  have ht : A.map φ * L.transpose = 1 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_map,
      Matrix.transpose_one] using congrArg Matrix.transpose hL
  intro v
  refine ⟨L.transpose *ᵥ v, ?_⟩
  rw [Matrix.mulVec_mulVec, ht, Matrix.one_mulVec]

theorem matrix_range_finrank_le_of_field_specialization
    (ψ : R →+* K) (φ : R →+* F) (hφ : Function.Injective φ)
    (A : Matrix a b R) :
    Module.finrank K (LinearMap.range (Matrix.toLin' (A.map ψ))) ≤
      Module.finrank F (LinearMap.range (Matrix.toLin' (A.map φ))) := by
  classical
  obtain ⟨c, f, hf, hs, hi⟩ := exists_linearIndependent' K (A.map ψ).col
  letI : Finite c := Finite.of_injective f hf
  letI : Fintype c := Fintype.ofFinite c
  let D : Matrix a c R := A.submatrix id f
  have hD : Function.Injective (D.map ψ).mulVec :=
    Matrix.mulVec_injective_iff.mpr hi
  have hD' := matrix_injective_of_field_specialization ψ φ hφ D hD
  have hi' := Matrix.mulVec_injective_iff.mp hD'
  rw [Matrix.range_toLin', Matrix.range_toLin', ← hs, finrank_span_eq_card hi]
  rw [← finrank_span_eq_card hi']
  apply Submodule.finrank_mono
  apply Submodule.span_mono
  rintro _ ⟨j, rfl⟩
  exact ⟨f j, rfl⟩

theorem matrix_kernel_finrank_le_of_field_specialization
    (ψ : R →+* K) (φ : R →+* F) (hφ : Function.Injective φ)
    (A : Matrix a b R) :
    Module.finrank F (LinearMap.ker (Matrix.toLin' (A.map φ))) ≤
      Module.finrank K (LinearMap.ker (Matrix.toLin' (A.map ψ))) := by
  have hr := matrix_range_finrank_le_of_field_specialization ψ φ hφ A
  have hK := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' (A.map ψ))
  have hF := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' (A.map φ))
  simp only [Module.finrank_fintype_fun_eq_card] at hK hF
  omega

end FD56
