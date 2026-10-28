/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericMinimal

/-! Pairwise degree balance determines the full Hilbert profile and the
degree multiset of an actual reduced polynomial kernel basis. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

theorem pairwise_balanced_degrees_hilbert {ι : Type*} [Fintype ι]
    (d : ι → ℕ) (hbalance : ∀ i j, d i ≤ d j + 1) (t : ℕ) :
    (∑ i, (t + 1 - d i)) = Fintype.card ι * (t + 1) - ∑ i, d i := by
  classical
  by_cases hle : ∀ i, d i ≤ t + 1
  · rw [Finset.sum_tsub_distrib _ (fun i _ => hle i)]
    simp
  · obtain ⟨i, hi⟩ := not_forall.mp hle
    have hge (j : ι) : t + 1 ≤ d j := by
      have := hbalance i j
      omega
    have hz : (∑ j, (t + 1 - d j)) = 0 :=
      Finset.sum_eq_zero (fun j _ => Nat.sub_eq_zero_of_le (hge j))
    have hsum : Fintype.card ι * (t + 1) ≤ ∑ j, d j := by
      simpa using Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hge j)
    rw [hz, Nat.sub_eq_zero_of_le hsum]

theorem pairwise_balanced_degrees_perm {k : ℕ} (hk : 0 < k)
    (d : Fin k → ℕ) (hbalance : ∀ i j, d i ≤ d j + 1) :
    (List.ofFn d).Perm (balancedDegreeList (∑ i, d i) k) := by
  apply listHilbert_determines_indices
  intro t
  rw [listHilbert_ofFn, listHilbert_nat, balancedDegreeList_hilbert _ _ _ hk]
  have h := pairwise_balanced_degrees_hilbert d hbalance t
  rw [Fintype.card_fin] at h
  exact_mod_cast h

theorem reduced_kernel_basis_balanced_minimal_degrees
    {K a b : Type*} [Field K] [Fintype b] [DecidableEq b]
    (A : Matrix a b K[X]) {k : ℕ} (hk : 0 < k)
    (B : Basis (Fin k) K[X] (LinearMap.ker (Matrix.toLin' A)))
    (d : Fin k → ℕ)
    (hdegree : ∀ i j, (polynomialKernelBasisMatrix A B i j).natDegree ≤ d j)
    (hlead : Function.Injective (Matrix.mulVec
      (fun i j => (polynomialKernelBasisMatrix A B i j).coeff (d j))))
    (hbalance : ∀ i j, d i ≤ d j + 1) :
    HasMinimalKernelDegrees A (balancedDegreeList (∑ i, d i) k) :=
  ⟨k, B, d, hdegree, hlead, pairwise_balanced_degrees_perm hk d hbalance⟩

end FD56
