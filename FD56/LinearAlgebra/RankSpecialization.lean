/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PolynomialBezout

/-! Full rank at one specialization implies full rank over any field
containing the coefficient ring. -/

noncomputable section
namespace FD56
open Matrix
variable {R K F a b : Type*} [CommRing R] [Field K] [Field F]
  [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

theorem det_ne_zero_of_specialization (ψ : R →+* K) (φ : R →+* F)
    (hφ : Function.Injective φ) (A : Matrix a a R)
    (hA : Matrix.det (A.map ψ) ≠ 0) : Matrix.det (A.map φ) ≠ 0 := by
  intro h
  have hzero : A.det = 0 := hφ (by simpa only [RingHom.map_det, map_zero] using h)
  apply hA
  calc
    Matrix.det (A.map ψ) = ψ A.det := (ψ.map_det A).symm
    _ = 0 := by rw [hzero, map_zero]

theorem matrix_injective_of_specialization (ι : K →+* R) (ψ : R →+* K)
    (hι : ∀ c, ψ (ι c) = c) (φ : R →+* F) (hφ : Function.Injective φ)
    (A : Matrix a b R) (hA : Function.Injective (A.map ψ).mulVec) :
    Function.Injective (A.map φ).mulVec := by
  obtain ⟨L, hL⟩ := matrix_left_inverse_of_injective (A.map ψ) hA
  let E := L.map ι
  have hE : E.map ψ = L := by ext i j; exact hι (L i j)
  have hd : Matrix.det ((E * A).map ψ) ≠ 0 := by
    rw [Matrix.map_mul, hE, hL, Matrix.det_one]
    exact one_ne_zero
  have hd' := det_ne_zero_of_specialization ψ φ hφ (E * A) hd
  rw [Matrix.map_mul] at hd'
  let Q := ((E.map φ) * (A.map φ))⁻¹ * E.map φ
  have hQ : Q * A.map φ = 1 := by
    rw [Matrix.mul_assoc]
    exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hd')
  intro v w h
  have hh := congrArg (fun z => Q *ᵥ z) h
  simpa only [Matrix.mulVec_mulVec, hQ, Matrix.one_mulVec] using hh

theorem matrix_surjective_of_specialization (ι : K →+* R) (ψ : R →+* K)
    (hι : ∀ c, ψ (ι c) = c) (φ : R →+* F) (hφ : Function.Injective φ)
    (A : Matrix a b R) (hA : Function.Surjective (A.map ψ).mulVec) :
    Function.Surjective (A.map φ).mulVec := by
  obtain ⟨g, hg⟩ := (Matrix.toLin' (A.map ψ)).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hA)
  let L := LinearMap.toMatrix' g
  have hL : A.map ψ * L = 1 := by
    simpa only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin',
      LinearMap.toMatrix'_id] using congrArg LinearMap.toMatrix' hg
  let E := L.map ι
  have hE : E.map ψ = L := by ext i j; exact hι (L i j)
  have hd : Matrix.det ((A * E).map ψ) ≠ 0 := by
    rw [Matrix.map_mul, hE, hL, Matrix.det_one]
    exact one_ne_zero
  have hd' := det_ne_zero_of_specialization ψ φ hφ (A * E) hd
  rw [Matrix.map_mul] at hd'
  let Q := E.map φ * ((A.map φ) * (E.map φ))⁻¹
  have hQ : A.map φ * Q = 1 := by
    rw [← Matrix.mul_assoc]
    exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hd')
  intro v
  refine ⟨Q *ᵥ v, ?_⟩
  rw [Matrix.mulVec_mulVec, hQ, Matrix.one_mulVec]

theorem matrix_transpose_injective_of_surjective (A : Matrix a b K)
    (hA : Function.Surjective A.mulVec) : Function.Injective A.transpose.mulVec := by
  obtain ⟨g, hg⟩ := (Matrix.toLin' A).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hA)
  let L := LinearMap.toMatrix' g
  have hL : A * L = 1 := by
    simpa only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin',
      LinearMap.toMatrix'_id] using congrArg LinearMap.toMatrix' hg
  have ht : L.transpose * A.transpose = 1 := by
    rw [← Matrix.transpose_mul, hL, Matrix.transpose_one]
  intro v w h
  have hh := congrArg (fun z => L.transpose *ᵥ z) h
  simpa only [Matrix.mulVec_mulVec, ht, Matrix.one_mulVec] using hh

end FD56
