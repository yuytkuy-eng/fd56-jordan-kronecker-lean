/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Restricting an alternating form to a hyperplane containing its radical
increases the radical dimension by exactly one. -/

noncomputable section
namespace FD56
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def hyperplaneRadical (B : V →ₗ[K] V →ₗ[K] K) (θ : V →ₗ[K] K) : Submodule K V where
  carrier := {x | θ x = 0 ∧ ∀ y, θ y = 0 → B x y = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro x y ⟨hx, hxB⟩ ⟨hy, hyB⟩
    constructor
    · simp [hx, hy]
    · intro z hz
      simp [hxB z hz, hyB z hz]
  smul_mem' := by
    rintro c x ⟨hx, hxB⟩
    constructor
    · simp [hx]
    · intro z hz
      simp [hxB z hz]

theorem functional_scalar_of_kernel (θ φ : V →ₗ[K] K) (hθ : θ ≠ 0)
    (h : ∀ x, θ x = 0 → φ x = 0) : ∃ c : K, φ = c • θ := by
  have hex : ∃ u, θ u ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hθ (LinearMap.ext hn)
  obtain ⟨u, hu⟩ := hex
  refine ⟨φ u / θ u, ?_⟩
  ext x
  have hx : θ (x - (θ x / θ u) • u) = 0 := by
    simp [hu]
  have hh := h _ hx
  simp only [map_sub, map_smul, smul_eq_mul] at hh
  change φ x = (φ u / θ u) * θ x
  field_simp at hh ⊢
  linear_combination hh

theorem alternating_neg_swap (B : V →ₗ[K] V →ₗ[K] K)
    (hB : ∀ x, B x x = 0) (x y : V) : -B x y = B y x := by
  have h := hB (x + y)
  simp only [map_add, LinearMap.add_apply, hB, zero_add, add_zero] at h
  exact neg_eq_iff_add_eq_zero.mpr (by simpa [add_comm] using h)

theorem exists_hyperplane_lift [FiniteDimensional K V]
    (B : V →ₗ[K] V →ₗ[K] K) (θ : V →ₗ[K] K)
    (hB : ∀ x, B x x = 0) (hker : LinearMap.ker B ≤ LinearMap.ker θ) :
    ∃ v, B v = θ ∧ θ v = 0 := by
  have hθ : θ ∈ (LinearMap.ker B).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro x hx
    exact hker hx
  rw [LinearMap.dualAnnihilator_ker_eq_range_flip] at hθ
  obtain ⟨w, hw⟩ := hθ
  have hv : B (-w) = θ := by
    ext y
    simp only [map_neg, LinearMap.neg_apply]
    rw [alternating_neg_swap B hB]
    exact congrArg (fun f : V →ₗ[K] K => f y) hw
  refine ⟨-w, hv, ?_⟩
  rw [← hv]
  exact hB (-w)

theorem hyperplane_radical_eq_sup [FiniteDimensional K V]
    (B : V →ₗ[K] V →ₗ[K] K) (θ : V →ₗ[K] K) (hθ : θ ≠ 0)
    (hB : ∀ x, B x x = 0) (hker : LinearMap.ker B ≤ LinearMap.ker θ)
    (v : V) (hv : B v = θ) :
    hyperplaneRadical B θ = LinearMap.ker B ⊔ Submodule.span K {v} := by
  have hθv : θ v = 0 := by rw [← hv]; exact hB v
  apply le_antisymm
  · intro x hx
    obtain ⟨c, hc⟩ := functional_scalar_of_kernel θ (B x) hθ hx.2
    have hz : x - c • v ∈ LinearMap.ker B := by
      change B (x - c • v) = 0
      simp [hc, hv]
    have hcv : c • v ∈ Submodule.span K {v} :=
      Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton v))
    have hh := Submodule.add_mem_sup hz hcv
    simpa using hh
  · apply sup_le
    · intro x hx
      refine ⟨hker hx, ?_⟩
      intro y _
      change B x = 0 at hx
      simp [hx]
    · apply Submodule.span_le.mpr
      intro x hx
      have : x = v := Set.mem_singleton_iff.mp hx
      subst x
      exact ⟨hθv, fun y hy => by rw [hv]; exact hy⟩

theorem hyperplane_radical_finrank [FiniteDimensional K V]
    (B : V →ₗ[K] V →ₗ[K] K) (θ : V →ₗ[K] K) (hθ : θ ≠ 0)
    (hB : ∀ x, B x x = 0) (hker : LinearMap.ker B ≤ LinearMap.ker θ) :
    Module.finrank K (hyperplaneRadical B θ) = Module.finrank K (LinearMap.ker B) + 1 := by
  obtain ⟨v, hv, _⟩ := exists_hyperplane_lift B θ hB hker
  have hvnot : v ∉ LinearMap.ker B := by
    intro h
    exact hθ (hv.symm.trans h)
  have hv0 : v ≠ 0 := by
    intro h
    apply hvnot
    simp [h]
  rw [hyperplane_radical_eq_sup B θ hθ hB hker v hv]
  have hdis := Submodule.disjoint_span_singleton_of_not_mem hvnot
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.ker B) (Submodule.span K {v})
  rw [hdis.eq_bot, finrank_span_singleton hv0] at hdim
  simpa using hdim

end FD56
