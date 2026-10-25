/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Tactic

/-! A dependent initial orbit spans an invariant subspace. -/

namespace FD56
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def krylovSpan (f : V →ₗ[K] V) (v : V) (q : ℕ) : Submodule K V :=
  Submodule.span K (Set.range (fun i : Fin q => (f^i.val) v))

theorem krylovSpan_power_mem (f : V →ₗ[K] V) (v : V) {q i : ℕ} (hi : i < q) :
    (f^i) v ∈ krylovSpan f v q :=
  Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩

theorem krylovSpan_mono (f : V →ₗ[K] V) (v : V) {q r : ℕ} (h : q ≤ r) :
    krylovSpan f v q ≤ krylovSpan f v r := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact krylovSpan_power_mem f v (lt_of_lt_of_le i.isLt h)

theorem krylovSpan_invariant_of_next_mem (f : V →ₗ[K] V) (v : V) (q : ℕ)
    (hnext : (f^q) v ∈ krylovSpan f v q) :
    ∀ w ∈ krylovSpan f v q, f w ∈ krylovSpan f v q := by
  have hle : krylovSpan f v q ≤ (krylovSpan f v q).comap f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change f ((f^i.val) v) ∈ krylovSpan f v q
    rw [← Module.End.mul_apply, ← pow_succ']
    by_cases hi : i.val + 1 < q
    · exact krylovSpan_power_mem f v hi
    · have he : i.val + 1 = q := by omega
      simpa only [he] using hnext
  exact fun w hw => hle hw

theorem krylovSpan_all_powers_of_next_mem (f : V →ₗ[K] V) (v : V) (q : ℕ)
    (hnext : (f^q) v ∈ krylovSpan f v q) (j : ℕ) :
    (f^j) v ∈ krylovSpan f v q := by
  have hv : v ∈ krylovSpan f v q := by
    cases q with
    | zero => simpa using hnext
    | succ q => simpa using krylovSpan_power_mem f v (Nat.zero_lt_succ q)
  induction j with
  | zero => simpa using hv
  | succ j ih =>
    simpa only [pow_succ', Module.End.mul_apply] using
      krylovSpan_invariant_of_next_mem f v q hnext _ ih

theorem krylovSpan_all_powers_of_dependent (f : V →ₗ[K] V) (v : V) (q : ℕ)
    (hdep : ¬ LinearIndependent K (fun i : Fin q => (f^i.val) v)) (j : ℕ) :
    (f^j) v ∈ krylovSpan f v q := by
  induction q with
  | zero => exact (hdep (linearIndependent_empty_type)).elim
  | succ q ih =>
    by_cases hp : LinearIndependent K (fun i : Fin q => (f^i.val) v)
    · have hnext : (f^q) v ∈ krylovSpan f v q := by
        by_contra hn
        apply hdep
        apply linearIndependent_fin_succ'.mpr
        exact ⟨by simpa [Fin.init] using hp, by simpa [krylovSpan, Fin.init] using hn⟩
      exact krylovSpan_mono f v (Nat.le_succ q)
        (krylovSpan_all_powers_of_next_mem f v q hnext j)
    · exact krylovSpan_mono f v (Nat.le_succ q) (ih hp)

theorem krylovSpan_invariant_of_dependent (f : V →ₗ[K] V) (v : V) (q : ℕ)
    (hdep : ¬ LinearIndependent K (fun i : Fin q => (f^i.val) v)) :
    ∀ w ∈ krylovSpan f v q, f w ∈ krylovSpan f v q :=
  krylovSpan_invariant_of_next_mem f v q (krylovSpan_all_powers_of_dependent f v q hdep q)

theorem krylovSpan_le_ker {W : Type*} [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] V) (v : V) (q : ℕ) (P : V →ₗ[K] W)
    (h : ∀ i < q, P ((f^i) v) = 0) : krylovSpan f v q ≤ LinearMap.ker P := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact h i.val i.isLt

theorem krylovSpan_ne_bot (f : V →ₗ[K] V) (v : V) {q : ℕ}
    (hq : 0 < q) (hv : v ≠ 0) : krylovSpan f v q ≠ ⊥ := by
  intro h
  have hm : v ∈ krylovSpan f v q := by simpa using krylovSpan_power_mem f v hq
  rw [h] at hm
  exact hv (by simpa using hm)

end FD56
