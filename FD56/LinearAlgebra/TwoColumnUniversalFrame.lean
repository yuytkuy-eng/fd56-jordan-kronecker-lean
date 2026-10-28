/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.TwoColumnPluckerNormalization
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.MvPolynomial.Eval

/-! Universal two-column polynomial frames and their nonzero leading pivots. -/

noncomputable section
namespace FD56
open Polynomial
open scoped BigOperators

abbrev TwoColumnCoefficientIndex (n : Type*) (a b : ℕ) :=
  (n × Fin (a+1)) ⊕ (n × Fin (b+1))

abbrev TwoColumnCoefficientRing (K n : Type*) [Field K] (a b : ℕ) :=
  MvPolynomial (TwoColumnCoefficientIndex n a b) K

abbrev TwoColumnCoefficientField (K n : Type*) [Field K] (a b : ℕ) :=
  FractionRing (TwoColumnCoefficientRing K n a b)

variable (K n : Type*) [Field K]

def twoColumnUniversalU (a b : ℕ) (i : n) : (TwoColumnCoefficientRing K n a b)[X] :=
  ∑ k : Fin (a+1), monomial k.val (MvPolynomial.X (Sum.inl (i,k)))

def twoColumnUniversalV (a b : ℕ) (i : n) : (TwoColumnCoefficientRing K n a b)[X] :=
  ∑ k : Fin (b+1), monomial k.val (MvPolynomial.X (Sum.inr (i,k)))

theorem twoColumnUniversalU_coeff (a b : ℕ) (i : n) (k : Fin (a+1)) :
    (twoColumnUniversalU K n a b i).coeff k.val=MvPolynomial.X (Sum.inl (i,k)) := by
  simp [twoColumnUniversalU,finset_sum_coeff,coeff_monomial,Fin.val_inj]

theorem twoColumnUniversalV_coeff (a b : ℕ) (i : n) (k : Fin (b+1)) :
    (twoColumnUniversalV K n a b i).coeff k.val=MvPolynomial.X (Sum.inr (i,k)) := by
  simp [twoColumnUniversalV,finset_sum_coeff,coeff_monomial,Fin.val_inj]

theorem twoColumnUniversalU_degree (a b : ℕ) (i : n) :
    (twoColumnUniversalU K n a b i).natDegree≤a := by
  apply natDegree_sum_le_of_forall_le
  intro k _
  exact (natDegree_monomial_le _).trans (by have := k.isLt; omega)

theorem twoColumnUniversalV_degree (a b : ℕ) (i : n) :
    (twoColumnUniversalV K n a b i).natDegree≤b := by
  apply natDegree_sum_le_of_forall_le
  intro k _
  exact (natDegree_monomial_le _).trans (by have := k.isLt; omega)

theorem two_column_universal_pivots (a b : ℕ) (i₀ i₁ : n) (hi : i₀≠i₁) :
    (twoColumnUniversalU K n a b i₀).coeff a≠0 ∧
    (twoColumnUniversalU K n a b i₀).coeff a*(twoColumnUniversalV K n a b i₁).coeff b-
      (twoColumnUniversalV K n a b i₀).coeff b*(twoColumnUniversalU K n a b i₁).coeff a≠0 := by
  classical
  have hu (i : n) : (twoColumnUniversalU K n a b i).coeff a=
      MvPolynomial.X (Sum.inl (i,Fin.last a)) := twoColumnUniversalU_coeff K n a b i (Fin.last a)
  have hv (i : n) : (twoColumnUniversalV K n a b i).coeff b=
      MvPolynomial.X (Sum.inr (i,Fin.last b)) := twoColumnUniversalV_coeff K n a b i (Fin.last b)
  simp only [hu,hv]
  constructor
  · exact MvPolynomial.X_ne_zero _
  · intro hz
    let value : TwoColumnCoefficientIndex n a b → K :=
      Sum.elim (fun ik => if ik.1=i₀ then 1 else 0) (fun ik => if ik.1=i₁ then 1 else 0)
    have h := congrArg (MvPolynomial.eval value) hz
    simpa [value,hi,Ne.symm hi] using h

def twoColumnFractionU (a b : ℕ) (i : n) : (TwoColumnCoefficientField K n a b)[X] :=
  (twoColumnUniversalU K n a b i).map (algebraMap _ _)

def twoColumnFractionV (a b : ℕ) (i : n) : (TwoColumnCoefficientField K n a b)[X] :=
  (twoColumnUniversalV K n a b i).map (algebraMap _ _)

theorem two_column_fraction_pivots (a b : ℕ) (i₀ i₁ : n) (hi : i₀≠i₁) :
    (twoColumnFractionU K n a b i₀).coeff a≠0 ∧
    (twoColumnFractionU K n a b i₀).coeff a*(twoColumnFractionV K n a b i₁).coeff b-
      (twoColumnFractionV K n a b i₀).coeff b*(twoColumnFractionU K n a b i₁).coeff a≠0 := by
  have hs := two_column_universal_pivots K n a b i₀ i₁ hi
  have hi' := IsFractionRing.injective (TwoColumnCoefficientRing K n a b)
    (TwoColumnCoefficientField K n a b)
  simp only [twoColumnFractionU,twoColumnFractionV,coeff_map,← map_mul,← map_sub]
  exact ⟨fun h => hs.1 (hi' (h.trans (map_zero _).symm)),
    fun h => hs.2 (hi' (h.trans (map_zero _).symm))⟩

theorem twoColumnFractionU_degree (a b : ℕ) (i : n) :
    (twoColumnFractionU K n a b i).natDegree≤a :=
  (natDegree_map_le).trans (twoColumnUniversalU_degree K n a b i)

theorem twoColumnFractionV_degree (a b : ℕ) (i : n) :
    (twoColumnFractionV K n a b i).natDegree≤b :=
  (natDegree_map_le).trans (twoColumnUniversalV_degree K n a b i)

end FD56
