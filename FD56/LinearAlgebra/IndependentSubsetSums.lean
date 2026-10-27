/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.FieldTheory.Separable
import Mathlib.Data.Set.Insert

/-! Distinct subsets give distinct sums of independent coordinates in every characteristic. -/

noncomputable section
namespace FD56
open scoped BigOperators

theorem mvPolynomial_subset_sum_injective {R σ : Type*}
    [CommSemiring R] [Nontrivial R] :
    Function.Injective (fun s : Finset σ => ∑ i ∈ s, (MvPolynomial.X i : MvPolynomial σ R)) := by
  classical
  intro s t h
  ext i
  have hc := congrArg (MvPolynomial.coeff (Finsupp.single i 1)) h
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_X',
    Finsupp.single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0)] at hc
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp_all

def scalarObservabilityPoleIndex (N : ℕ) := Fin N ⊕ (Σ i : Fin N, {j : Fin N // i < j})

instance (N : ℕ) : Fintype (scalarObservabilityPoleIndex N) :=
  inferInstanceAs (Fintype (Fin N ⊕ (Σ i : Fin N, {j : Fin N // i < j})))

def scalarObservabilityPoleSupport {N : ℕ} : scalarObservabilityPoleIndex N → Finset (Fin N)
  | .inl i => {i}
  | .inr ⟨i,j⟩ => {i,j.val}

theorem scalarObservabilityPoleSupport_injective (N : ℕ) :
    Function.Injective (@scalarObservabilityPoleSupport N) := by
  intro a b h
  rcases a with i | ⟨i,j,hij⟩ <;> rcases b with k | ⟨k,l,hkl⟩
  · congr 1
    simpa [scalarObservabilityPoleSupport] using h
  · have hk : k = i := by
      have := congrArg (fun s => k ∈ s) h
      simpa [scalarObservabilityPoleSupport] using this.symm
    have hl : l = i := by
      have := congrArg (fun s => l ∈ s) h
      simpa [scalarObservabilityPoleSupport] using this.symm
    omega
  · have hi : i = k := by
      have := congrArg (fun s => i ∈ s) h
      simpa [scalarObservabilityPoleSupport] using this
    have hj : j = k := by
      have := congrArg (fun s => j ∈ s) h
      simpa [scalarObservabilityPoleSupport] using this
    omega
  · have hs : ({i,j} : Set (Fin N)) = {k,l} := by
      simpa [scalarObservabilityPoleSupport] using congrArg (fun s : Finset (Fin N) => (s : Set (Fin N))) h
    rcases Set.pair_eq_pair_iff.mp hs with ⟨hi,hj⟩ | ⟨hi,hj⟩
    · subst k
      subst l
      rfl
    · omega

theorem independent_scalar_observability_poles_injective {K F : Type*}
    [Field K] [Field F] (N : ℕ)
    (ι : MvPolynomial (Fin N) K →+* F) (hι : Function.Injective ι) :
    Function.Injective (fun a : scalarObservabilityPoleIndex N =>
      -(∑ i ∈ scalarObservabilityPoleSupport a, ι (MvPolynomial.X i))) := by
  intro a b h
  apply scalarObservabilityPoleSupport_injective N
  apply mvPolynomial_subset_sum_injective (R := K)
  apply hι
  simpa only [map_sum] using neg_injective h

end FD56
