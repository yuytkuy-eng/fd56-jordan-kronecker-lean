/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PolynomialDerivationImage
import FD56.LinearAlgebra.DerivationAlgebraicIndependence

/-! On the coprime polynomial chart of the Plucker quadric, four coordinate
polynomials and one leading coefficient detect every coefficient derivation.
A sharp derivative rank then makes these chart coordinates algebraically independent. -/

noncomputable section
namespace FD56
open Polynomial

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

abbrev PluckerChartIndex (W : ℕ) := (Fin 4 × Fin (W+1)) ⊕ Unit

def pluckerChartCoefficientMap (W : ℕ) :
    (Fin 6 → L[X]) →ₗ[L] (PluckerChartIndex W → L) where
  toFun F := fun i => match i with
    | Sum.inl j => (F (j.1.castAdd 2)).coeff j.2.val
    | Sum.inr _ => (F 4).coeff W
  map_add' F G := by funext i; cases i <;> simp
  map_smul' c F := by funext i; cases i <;> simp

def pluckerChartCoordinates (W : ℕ) (F : Fin 6 → L[X]) : PluckerChartIndex W → L :=
  pluckerChartCoefficientMap W F

def pluckerChartImageMap (W : ℕ) (F : Fin 6 → L[X]) :
    LinearMap.range (polynomialDerivationImageMap (K:=K) F) →ₗ[L]
      (PluckerChartIndex W → L) :=
  (pluckerChartCoefficientMap W).comp (LinearMap.range
    (polynomialDerivationImageMap (K:=K) F)).subtype

private theorem coprime_tangent_zero (W : ℕ) (F H : Fin 6 → L[X])
    (hF0 : F 0 ≠ 0) (hdegree : (F 0).natDegree=W)
    (hcoprime : IsCoprime (F 0) (F 1))
    (hH4 : (H 4).natDegree ≤ W) (hcoeff : (H 4).coeff W=0)
    (hrel : F 0*H 5=F 1*H 4) : H 4=0 ∧ H 5=0 := by
  have hdvd : F 0 ∣ H 4 := hcoprime.dvd_of_dvd_mul_left ⟨H 5,hrel.symm⟩
  have hzero : H 4=0 := by
    by_contra hn
    obtain ⟨p,hp⟩ := hdvd
    have hp0 : p≠0 := by intro hz; rw [hz,mul_zero] at hp; exact hn hp
    have hge : W ≤ (H 4).natDegree := by
      rw [hp,Polynomial.natDegree_mul hF0 hp0,hdegree]
      omega
    have heq := Nat.le_antisymm hH4 hge
    have hlead : (H 4).leadingCoeff=0 := by
      simpa only [Polynomial.leadingCoeff,heq] using hcoeff
    exact (Polynomial.leadingCoeff_ne_zero.mpr hn) hlead
  refine ⟨hzero,?_⟩
  rw [hzero,mul_zero] at hrel
  exact (mul_eq_zero.mp hrel).resolve_left hF0

private theorem chart_map_derivation (W : ℕ) (F : Fin 6 → L[X])
    (D : Derivation K L L) :
    pluckerChartCoefficientMap W (polynomialDerivationImageMap F D)=
      fun i => D (pluckerChartCoordinates W F i) := by
  funext i
  cases i <;> rfl

theorem pluckerChartImageMap_injective (W : ℕ) (F : Fin 6 → L[X])
    (hdegree : ∀ i, (F i).natDegree ≤ W)
    (hF0 : F 0 ≠ 0) (hfirst : (F 0).natDegree=W)
    (hcoprime : IsCoprime (F 0) (F 1))
    (hquadric : F 0*F 5-F 1*F 4+F 2*F 3=0) :
    Function.Injective (pluckerChartImageMap (K:=K) W F) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  rintro ⟨p,⟨D,rfl⟩⟩ hp
  let H : Fin 6 → L[X] := polynomialDerivationImageMap F D
  have hcoord : pluckerChartCoefficientMap W H=0 := hp
  have hHdegree (i : Fin 6) : (H i).natDegree≤W :=
    polynomialCoefficientDerivation_degree_bound D (F i) W (hdegree i)
  have hsmall (i : Fin 4) : H (i.castAdd 2)=0 := by
    apply Polynomial.ext
    intro k
    by_cases hk : k<W+1
    · have h := congrFun hcoord (Sum.inl (i,⟨k,hk⟩))
      exact h
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by have := hHdegree (i.castAdd 2); omega)]
      rfl
  have hcoeff : (H 4).coeff W=0 := congrFun hcoord (Sum.inr ())
  have hrel : F 0*H 5=F 1*H 4 := by
    have h := congrArg (polynomialCoefficientDerivation D) hquadric
    simp only [map_add,map_sub,Derivation.leibniz,map_zero,smul_eq_mul] at h
    change F 0*H 5+F 5*H 0-(F 1*H 4+F 4*H 1)+(F 2*H 3+F 3*H 2)=0 at h
    have h0 : H 0=0 := hsmall 0
    have h1 : H 1=0 := hsmall 1
    have h2 : H 2=0 := hsmall 2
    have h3 : H 3=0 := hsmall 3
    simpa only [h0,h1,h2,h3,mul_zero,add_zero,sub_eq_zero] using h
  obtain ⟨h4,h5⟩ := coprime_tangent_zero W F H hF0 hfirst hcoprime (hHdegree 4) hcoeff hrel
  apply Subtype.ext
  change H=0
  funext i
  fin_cases i
  · exact hsmall 0
  · exact hsmall 1
  · exact hsmall 2
  · exact hsmall 3
  · exact h4
  · exact h5

theorem pluckerChart_derivation_values_surjective (W : ℕ) (F : Fin 6 → L[X])
    (hdegree : ∀ i, (F i).natDegree ≤ W)
    (hF0 : F 0 ≠ 0) (hfirst : (F 0).natDegree=W)
    (hcoprime : IsCoprime (F 0) (F 1))
    (hquadric : F 0*F 5-F 1*F 4+F 2*F 3=0)
    (hrank : 4*(W+1)+1 ≤ Module.finrank L
      (LinearMap.range (polynomialDerivationImageMap (K:=K) F))) :
    ∀ v : PluckerChartIndex W → L, ∃ D : Derivation K L L,
      ∀ i, D (pluckerChartCoordinates W F i)=v i := by
  let E := pluckerChartImageMap (K:=K) W F
  have hinj : Function.Injective E :=
    pluckerChartImageMap_injective W F hdegree hF0 hfirst hcoprime hquadric
  letI := FiniteDimensional.of_injective E hinj
  have hdim : Module.finrank L (PluckerChartIndex W → L)=4*(W+1)+1 := by
    simp [PluckerChartIndex, Module.finrank_fintype_fun_eq_card]
  have heq : Module.finrank L (LinearMap.range (polynomialDerivationImageMap (K:=K) F))=
      Module.finrank L (PluckerChartIndex W → L) := by
    apply Nat.le_antisymm (LinearMap.finrank_le_finrank_of_injective hinj)
    rw [hdim]
    exact hrank
  have hsurj : Function.Surjective E :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mp hinj
  intro v
  obtain ⟨p,hp⟩ := hsurj v
  obtain ⟨D,hD⟩ := p.property
  refine ⟨D,?_⟩
  have h : pluckerChartCoefficientMap W (polynomialDerivationImageMap F D)=v := by
    rw [hD]
    exact hp
  rw [chart_map_derivation] at h
  exact congrFun h

theorem pluckerChart_coordinates_algebraicIndependent [CharZero K]
    (W : ℕ) (F : Fin 6 → L[X])
    (hdegree : ∀ i, (F i).natDegree ≤ W)
    (hF0 : F 0 ≠ 0) (hfirst : (F 0).natDegree=W)
    (hcoprime : IsCoprime (F 0) (F 1))
    (hquadric : F 0*F 5-F 1*F 4+F 2*F 3=0)
    (hrank : 4*(W+1)+1 ≤ Module.finrank L
      (LinearMap.range (polynomialDerivationImageMap (K:=K) F))) :
    AlgebraicIndependent K (pluckerChartCoordinates W F) :=
  algebraicIndependent_of_derivation_values_surjective _
    (pluckerChart_derivation_values_surjective W F hdegree hF0 hfirst hcoprime hquadric hrank)

end FD56
