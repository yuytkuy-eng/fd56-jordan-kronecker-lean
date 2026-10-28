/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PolynomialRowProjection
import Mathlib.Algebra.Polynomial.AlgebraMap

/-! Polynomial functionals over an extension field have coprime values on
base-field vectors while avoiding finitely many proper base-field subspaces. -/

noncomputable section
namespace FD56
open Polynomial
open scoped BigOperators

variable {K L V : Type*} [Field K] [Infinite K] [Field L] [Algebra K L]
  [AddCommGroup V] [Module K V]

theorem exists_coprime_polynomial_linear_map_avoiding
    (F : V →ₗ[K] L[X]) (f : L[X]) (hf : f≠0)
    (hprimitive : ∀ p : L[X], Irreducible p → p∣f → ∃ v : V, ¬p∣F v)
    (s : Finset (Submodule K V)) (hs : ∀ S∈s, S≠⊤) :
    ∃ v : V, IsCoprime f (F v) ∧ ∀ S∈s, v∉S := by
  classical
  let bad (p : L[X]) : Submodule K V :=
    ((Ideal.span ({p} : Set L[X])).restrictScalars K).comap F
  have hbad (p : L[X]) (v : V) : v∈bad p ↔ p∣F v := Ideal.mem_span_singleton
  let factors := (UniqueFactorizationMonoid.normalizedFactors f).toFinset
  have hproper (p : L[X]) (hp : p∈factors) : bad p≠⊤ := by
    have hmem := Multiset.mem_toFinset.mp hp
    obtain ⟨v,hv⟩ := hprimitive p
      (UniqueFactorizationMonoid.irreducible_of_normalized_factor p hmem)
      (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hmem)
    intro he
    apply hv
    apply (hbad p v).mp
    rw [he]
    trivial
  obtain ⟨v,hv⟩ := exists_avoiding_finite_submodules (s ∪ factors.image bad) (by
    intro S hS
    rcases Finset.mem_union.mp hS with hS | hS
    · exact hs S hS
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hS
      exact hproper p hp)
  refine ⟨v,?_,fun S hS => hv S (Finset.mem_union_left _ hS)⟩
  apply isCoprime_of_irreducible_dvd (fun h => hf h.1)
  intro p hp hpf hpF
  obtain ⟨d,hd,hpd⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hf hp hpf
  apply hv (bad d) (Finset.mem_union_right _
    (Finset.mem_image.mpr ⟨d,Multiset.mem_toFinset.mpr hd,rfl⟩))
  exact (hbad d v).mpr (hpd.dvd_iff_dvd_left.mp hpF)

theorem exists_coprime_constant_polynomial_functional_avoiding
    {m : Type*} [Fintype m] (h a : m → L[X]) (hunit : ∑ i, h i*a i=1)
    (f : L[X]) (hf : f≠0)
    (s : Finset (Submodule K (m → K))) (hs : ∀ S∈s, S≠⊤) :
    ∃ w : m → K,
      IsCoprime f (∑ i, C (algebraMap K L (w i))*h i) ∧ ∀ S∈s, w∉S := by
  classical
  let F : (m → K) →ₗ[K] L[X] :=
    { toFun := fun w => ∑ i, w i • h i
      map_add' := by intro u v; simp [add_smul,Finset.sum_add_distrib]
      map_smul' := by intro c u; simp [smul_smul,Finset.smul_sum] }
  have hsingle (i : m) : F (Pi.single i 1)=h i := by simp [F,Pi.single_apply]
  have hprimitive (p : L[X]) (hp : Irreducible p) (_ : p∣f) :
      ∃ v : m → K, ¬p∣F v := by
    by_contra! hz
    have hd (i : m) : p∣h i := by simpa only [hsingle] using hz (Pi.single i 1)
    have hone : p∣(1 : L[X]) := by
      rw [← hunit]
      exact Finset.dvd_sum (fun i _ => dvd_mul_of_dvd_left (hd i) (a i))
    exact hp.not_isUnit (isUnit_of_dvd_one hone)
  obtain ⟨w,hw,hws⟩ := exists_coprime_polynomial_linear_map_avoiding F f hf hprimitive s hs
  refine ⟨w,?_,hws⟩
  simpa only [F,LinearMap.coe_mk,AddHom.coe_mk,Algebra.smul_def,
    Polynomial.algebraMap_apply] using hw

end FD56
