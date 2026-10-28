/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Arithmetic.DegreeEndomorphismBudget
import FD56.LinearAlgebra.PredictableDegree

/-! Polynomial changes of a column frame which preserve its individual degree
bounds. Their dimension is the degree-endomorphism budget, including entries
whose allowed coefficient space has dimension zero. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K n j : Type*} [Field K] [Fintype j]

abbrev WeightedPolynomialEndomorphisms (K : Type*) [Field K] (d : j → ℕ) :=
  ∀ i j, Polynomial.degreeLT K (degreeHomWeight (d i) (d j))

local instance degreeLTFinite (k : ℕ) : Module.Finite K (Polynomial.degreeLT K k) :=
  Module.Finite.of_injective (Polynomial.degreeLTEquiv K k).toLinearMap
    (Polynomial.degreeLTEquiv K k).injective

instance weightedPolynomialEndomorphismsFinite (d : j → ℕ) :
    Module.Finite K (WeightedPolynomialEndomorphisms K d) := by
  unfold WeightedPolynomialEndomorphisms
  infer_instance

theorem weightedPolynomialEndomorphisms_finrank (d : j → ℕ) :
    Module.finrank K (WeightedPolynomialEndomorphisms K d) =
      degreeEndomorphismDimension d := by
  unfold WeightedPolynomialEndomorphisms degreeEndomorphismDimension
  rw [Module.finrank_pi_fintype]
  apply Finset.sum_congr rfl
  intro i _
  rw [Module.finrank_pi_fintype]
  apply Finset.sum_congr rfl
  intro j _
  rw [(Polynomial.degreeLTEquiv K _).finrank_eq]
  simp

def weightedEndomorphismEntries (d : j → ℕ) (H : WeightedPolynomialEndomorphisms K d) :
    Matrix j j K[X] := fun i j => (H i j).val

omit [Fintype j] in
theorem weightedEndomorphism_entry_degree (d : j → ℕ)
    (H : WeightedPolynomialEndomorphisms K d) (i j : j) :
    weightedEndomorphismEntries d H i j = 0 ∨
      (d i ≤ d j ∧ (weightedEndomorphismEntries d H i j).natDegree ≤ d j-d i) := by
  by_cases hij : d i ≤ d j
  · right
    refine ⟨hij, ?_⟩
    have hp : (H i j).val ∈ Polynomial.degreeLT K (d j-d i+1) := by
      simpa [degreeHomWeight,hij] using (H i j).property
    exact boundedPoly_degree (d j-d i) ⟨(H i j).val,hp⟩
  · left
    have hp : (H i j).val ∈ Polynomial.degreeLT K 0 := by
      simpa [degreeHomWeight,hij] using (H i j).property
    change (H i j).val = 0
    by_contra hn
    have hd := Polynomial.mem_degreeLT.mp hp
    rw [Polynomial.degree_eq_natDegree hn,Nat.cast_lt] at hd
    omega

theorem weightedEndomorphism_trace_constant (d : j → ℕ)
    (H : WeightedPolynomialEndomorphisms K d) :
    Matrix.trace (weightedEndomorphismEntries d H) =
      C (∑ i, (weightedEndomorphismEntries d H i i).coeff 0) := by
  classical
  simp only [Matrix.trace,Matrix.diag_apply,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rcases weightedEndomorphism_entry_degree d H i i with hz | ⟨_,hdeg⟩
  · simp [hz]
  · exact Polynomial.eq_C_of_natDegree_le_zero (by simpa using hdeg)

theorem weightedEndomorphism_mul_degree (V : Matrix n j K[X]) (d : j → ℕ)
    (hdegree : ∀ i j, (V i j).natDegree ≤ d j)
    (H : WeightedPolynomialEndomorphisms K d) (i : n) (j : j) :
    ((V * weightedEndomorphismEntries d H) i j).natDegree ≤ d j :=
  polynomial_combination_degree_bound V d
    (fun k => weightedEndomorphismEntries d H k j) (d j) hdegree
    (fun k => weightedEndomorphism_entry_degree d H k j) i

def weightedEndomorphismVariation (V : Matrix n j K[X]) (d : j → ℕ)
    (hdegree : ∀ i j, (V i j).natDegree ≤ d j) :
    WeightedPolynomialEndomorphisms K d →ₗ[K] (∀ (_i : n) (j : j), BoundedPoly K (d j)) where
  toFun H i j := boundedPolyOf ((V * weightedEndomorphismEntries d H) i j)
    (weightedEndomorphism_mul_degree V d hdegree H i j)
  map_add' H G := by
    funext i j
    apply Subtype.ext
    change (V * (weightedEndomorphismEntries d H + weightedEndomorphismEntries d G)) i j = _
    rw [Matrix.mul_add]
    rfl
  map_smul' c H := by
    funext i j
    apply Subtype.ext
    change (V * (c • weightedEndomorphismEntries d H)) i j = _
    rw [Matrix.mul_smul]
    rfl

theorem weightedEndomorphismVariation_injective (V : Matrix n j K[X]) (d : j → ℕ)
    (hdegree : ∀ i j, (V i j).natDegree ≤ d j)
    (hV : Function.Injective V.mulVec) :
    Function.Injective (weightedEndomorphismVariation V d hdegree) := by
  intro H G h
  funext i j
  apply Subtype.ext
  have hcol : (fun k => weightedEndomorphismEntries d H k j) =
      (fun k => weightedEndomorphismEntries d G k j) := by
    apply hV
    funext k
    exact congrArg Subtype.val (congrFun (congrFun h k) j)
  exact congrFun hcol i

theorem weightedEndomorphismVariation_finrank_range (V : Matrix n j K[X]) (d : j → ℕ)
    (hdegree : ∀ i j, (V i j).natDegree ≤ d j)
    (hV : Function.Injective V.mulVec) :
    Module.finrank K (LinearMap.range (weightedEndomorphismVariation V d hdegree)) =
      degreeEndomorphismDimension d := by
  rw [LinearMap.finrank_range_of_inj
    (weightedEndomorphismVariation_injective V d hdegree hV)]
  exact weightedPolynomialEndomorphisms_finrank d

end FD56
