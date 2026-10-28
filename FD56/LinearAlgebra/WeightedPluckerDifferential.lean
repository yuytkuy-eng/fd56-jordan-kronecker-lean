/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PluckerDifferential
import FD56.LinearAlgebra.WeightedPolynomialEndomorphisms

/-! The finite rank bound for a scaled Plucker differential with individual
column degree bounds. Weighted changes of frame give an explicit kernel. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K m r : Type*} [Field K] [Fintype r] [DecidableEq r]

abbrev WeightedPluckerDomain (K : Type*) [Field K] (m : Type*) (d : r → ℕ) :=
  K × (∀ (_i : m) (j : r), BoundedPoly K (d j))

def weightedPluckerEntries (d : r → ℕ) :
    (∀ (_i : m) (j : r), BoundedPoly K (d j)) →ₗ[K] Matrix m r K[X] where
  toFun E i j := (E i j).val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def weightedPluckerInputs (d : r → ℕ) :
    WeightedPluckerDomain K m d →ₗ[K] (K[X] × Matrix m r K[X]) :=
  (Algebra.linearMap K K[X]).prodMap (weightedPluckerEntries d)

def weightedPluckerDifferential (c : K) (G : Matrix m r K[X]) (d : r → ℕ) :
    WeightedPluckerDomain K m d →ₗ[K] ((r → m) → K[X]) :=
  ((pluckerScalarDifferential (C c) G).restrictScalars K).comp (weightedPluckerInputs d)

theorem weightedPluckerDifferential_apply (c : K) (G : Matrix m r K[X]) (d : r → ℕ)
    (x : WeightedPluckerDomain K m d) :
    weightedPluckerDifferential c G d x=
      pluckerScalarDifferential (C c) G (C x.1,weightedPluckerEntries d x.2) := rfl

def weightedEndomorphismTrace (d : r → ℕ) : WeightedPolynomialEndomorphisms K d →ₗ[K] K where
  toFun H := ∑ i, (weightedEndomorphismEntries d H i i).coeff 0
  map_add' H J := by
    change (∑ i, ((H i i).val+(J i i).val).coeff 0)=_
    simp only [Polynomial.coeff_add,Finset.sum_add_distrib]
    rfl
  map_smul' c H := by
    change (∑ i, (c • (H i i).val).coeff 0)=_
    simp only [Polynomial.coeff_smul,← Finset.smul_sum]
    rfl

def weightedPluckerEndomorphism (c : K) (G : Matrix m r K[X]) (d : r → ℕ)
    (hdegree : ∀ i j, (G i j).natDegree ≤ d j) :
    WeightedPolynomialEndomorphisms K d →ₗ[K] WeightedPluckerDomain K m d :=
  (-c • weightedEndomorphismTrace d).prod (weightedEndomorphismVariation G d hdegree)

omit [DecidableEq r] in
theorem weightedPluckerEndomorphism_injective (c : K) (G : Matrix m r K[X]) (d : r → ℕ)
    (hdegree : ∀ i j, (G i j).natDegree ≤ d j) (hG : Function.Injective G.mulVec) :
    Function.Injective (weightedPluckerEndomorphism c G d hdegree) := by
  intro H J h
  apply weightedEndomorphismVariation_injective G d hdegree hG
  exact congrArg Prod.snd h

theorem weightedPluckerDifferential_endomorphism_zero
    (c : K) (G : Matrix m r K[X]) (d : r → ℕ)
    (hdegree : ∀ i j, (G i j).natDegree ≤ d j)
    (H : WeightedPolynomialEndomorphisms K d) :
    weightedPluckerDifferential c G d (weightedPluckerEndomorphism c G d hdegree H)=0 := by
  rw [weightedPluckerDifferential_apply]
  change pluckerScalarDifferential (C c) G
    (C (-c*(∑ i, (weightedEndomorphismEntries d H i i).coeff 0)),
      G*weightedEndomorphismEntries d H)=0
  rw [Polynomial.C_mul,Polynomial.C_neg,← weightedEndomorphism_trace_constant d H]
  exact pluckerScalarDifferential_endomorphism_zero (C c) G (weightedEndomorphismEntries d H)

theorem weightedPluckerEndomorphism_range_le_ker
    (c : K) (G : Matrix m r K[X]) (d : r → ℕ)
    (hdegree : ∀ i j, (G i j).natDegree ≤ d j) :
    LinearMap.range (weightedPluckerEndomorphism c G d hdegree) ≤
      LinearMap.ker (weightedPluckerDifferential c G d) := by
  rintro x ⟨H,rfl⟩
  exact weightedPluckerDifferential_endomorphism_zero c G d hdegree H

variable [Fintype m]

omit [DecidableEq r] in
theorem weightedPluckerDomain_finrank (d : r → ℕ) :
    Module.finrank K (WeightedPluckerDomain K m d)=
      1+Fintype.card m*(∑ j, (d j+1)) := by
  simp only [WeightedPluckerDomain,Module.finrank_prod,Module.finrank_self,
    Module.finrank_pi_fintype,boundedPoly_finrank,Finset.sum_const,
    Finset.card_univ,smul_eq_mul]

theorem weightedPluckerDifferential_finrank_range_bound
    (c : K) (G : Matrix m r K[X]) (d : r → ℕ)
    (hdegree : ∀ i j, (G i j).natDegree ≤ d j) (hG : Function.Injective G.mulVec) :
    Module.finrank K (LinearMap.range (weightedPluckerDifferential c G d))+
      degreeEndomorphismDimension d ≤ 1+Fintype.card m*(∑ j, (d j+1)) := by
  have he : Module.finrank K
      (LinearMap.range (weightedPluckerEndomorphism c G d hdegree))=
      degreeEndomorphismDimension d := by
    rw [LinearMap.finrank_range_of_inj
      (weightedPluckerEndomorphism_injective c G d hdegree hG)]
    exact weightedPolynomialEndomorphisms_finrank d
  have hk := Submodule.finrank_mono
    (weightedPluckerEndomorphism_range_le_ker c G d hdegree)
  rw [he] at hk
  have hb := (weightedPluckerDifferential c G d).finrank_range_add_finrank_ker
  rw [weightedPluckerDomain_finrank] at hb
  omega

theorem weightedPluckerDifferential_postcomp_finrank_range_bound
    {W : Type*} [AddCommGroup W] [Module K W]
    (T : ((r → m) → K[X]) →ₗ[K] W)
    (c : K) (G : Matrix m r K[X]) (d : r → ℕ)
    (hdegree : ∀ i j, (G i j).natDegree ≤ d j) (hG : Function.Injective G.mulVec) :
    Module.finrank K (LinearMap.range (T.comp (weightedPluckerDifferential c G d)))+
      degreeEndomorphismDimension d ≤ 1+Fintype.card m*(∑ j, (d j+1)) := by
  have hr := Submodule.finrank_map_le T
    (LinearMap.range (weightedPluckerDifferential c G d))
  rw [← LinearMap.range_comp] at hr
  exact (Nat.add_le_add_right hr _).trans
    (weightedPluckerDifferential_finrank_range_bound c G d hdegree hG)

end FD56
