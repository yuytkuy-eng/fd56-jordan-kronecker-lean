/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.SeparableDeterminant
import Mathlib.RingTheory.Localization.Away.Basic

/-! Separability transfers from a specialization that preserves the leading coefficient. -/

noncomputable section
namespace FD56
open Polynomial

theorem separable_of_specialization {R F L : Type*}
    [CommRing R] [Field F] [Field L]
    (f : R[X]) (φ : R →+* L) (ψ : R →+* F)
    (hψ : Function.Injective ψ) (hφ : φ f.leadingCoeff ≠ 0)
    (hs : (f.map φ).Separable) : (f.map ψ).Separable := by
  let S := Localization.Away f.leadingCoeff
  let φ' : S →+* L := IsLocalization.Away.lift f.leadingCoeff
    (isUnit_iff_ne_zero.mpr hφ)
  have hψlc : ψ f.leadingCoeff ≠ 0 := by
    intro h
    have hz := hψ (h.trans (map_zero ψ).symm)
    exact hφ (by rw [hz, map_zero])
  let ψ' : S →+* F := IsLocalization.Away.lift f.leadingCoeff
    (isUnit_iff_ne_zero.mpr hψlc)
  have hψ' : Function.Injective ψ' := by
    rw [IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers f.leadingCoeff)]
    intro x y
    constructor
    · exact congrArg ψ'
    · intro h
      apply congrArg (algebraMap R S)
      apply hψ
      simpa only [ψ', IsLocalization.Away.lift_eq] using h
  letI : Nontrivial S := φ'.domain_nontrivial
  have hu : IsUnit (algebraMap R S f.leadingCoeff) :=
    IsLocalization.Away.algebraMap_isUnit f.leadingCoeff
  let u : Sˣ := hu.unit
  let g : S[X] := f.map (algebraMap R S) * C (↑u⁻¹ : S)
  have hg : g.Monic := by
    apply monic_mul_C_of_leadingCoeff_mul_eq_one
    rw [leadingCoeff_map_of_leadingCoeff_ne_zero _ hu.ne_zero]
    change algebraMap R S f.leadingCoeff * ↑u⁻¹ = 1
    rw [← hu.unit_spec]
    exact Units.mul_inv u
  have hmapφ : g.map φ' = f.map φ * C (φ' ↑u⁻¹) := by
    simp only [g, Polynomial.map_mul, map_map, map_C, φ',
      IsLocalization.Away.lift_comp]
  have hmapψ : g.map ψ' = f.map ψ * C (ψ' ↑u⁻¹) := by
    simp only [g, Polynomial.map_mul, map_map, map_C, ψ',
      IsLocalization.Away.lift_comp]
  have hgφ : (g.map φ').Separable := by
    rw [hmapφ]
    exact hs.mul_unit (isUnit_C.mpr ((u⁻¹).isUnit.map φ'))
  have hgψ := monic_separable_of_specialization g hg φ' ψ' hψ' hgφ
  rw [hmapψ] at hgψ
  exact hgψ.of_mul_left

theorem separable_of_degree_preserving_specialization {R F L : Type*}
    [CommRing R] [Field F] [Field L]
    (f : R[X]) (φ : R →+* L) (ψ : R →+* F)
    (hψ : Function.Injective ψ) (hd : (f.map φ).natDegree = f.natDegree)
    (hs : (f.map φ).Separable) : (f.map ψ).Separable := by
  apply separable_of_specialization f φ ψ hψ _ hs
  intro hz
  have hn : f.map φ ≠ 0 := hs.ne_zero
  have hlt := natDegree_map_lt hz hn
  omega

end FD56
