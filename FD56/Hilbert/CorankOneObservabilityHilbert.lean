/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.CorankOneObservabilityAllDepths
import FD56.Hilbert.ObservabilityBetaDimension
import FD56.Hilbert.ObservabilityBetaEvaluation

/-! Exact bounded auxiliary relation dimensions in every corank-one depth. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

theorem corank_one_observability_beta_degree_pos (q m : ℕ) (hm : 2 ≤ m) :
    0 < m*(∑ i : Fin (q+1), (i.val+1))-(q+1) := by
  have hs : q+1 ≤ ∑ i : Fin (q+1), (i.val+1) := by
    calc
      q+1 = ∑ _i : Fin (q+1), 1 := by simp
      _ ≤ ∑ i : Fin (q+1), (i.val+1) := Finset.sum_le_sum (by intros; omega)
  have : q+1 < m*(∑ i : Fin (q+1), (i.val+1)) := by nlinarith
  omega

variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem generic_corank_one_all_depths_bounded_beta_hilbert (q d : ℕ)
    (hm : 2 ≤ Fintype.card m)
    (hn : Fintype.card n+1=(q+1)*Fintype.card m) :
    Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (boundedObservabilityBetaKernel q (genericAffineSquare K n m) (genericAffineRows K n m) d) =
    d+1-(Fintype.card m*(∑ i : Fin (q+1), (i.val+1))-(q+1)) := by
  let D := Fintype.card m*(∑ i : Fin (q+1), (i.val+1))-(q+1)
  have hD : 0 < D := corank_one_observability_beta_degree_pos q _ hm
  have hlo : q*Fintype.card m ≤ Fintype.card n := by nlinarith
  have hhi : Fintype.card n ≤ (q+1)*Fintype.card m := by omega
  have hgap : (q+1)*Fintype.card m-Fintype.card n=1 := by omega
  have hupper (d : ℕ) : Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (boundedObservabilityBetaKernel q (genericAffineSquare K n m) (genericAffineRows K n m) d) ≤
      d+1-D := by
    induction d with
    | zero =>
      rw [generic_corank_one_all_depths_beta_zero q 0 hm hn hD]
      exact Nat.zero_le _
    | succ d ih =>
      by_cases hd : d+1<D
      · rw [generic_corank_one_all_depths_beta_zero q (d+1) hm hn hd]
        exact Nat.zero_le _
      · have hh := generic_bounded_observability_beta_growth (K := K) q hlo hhi d
        rw [hgap] at hh
        omega
  apply le_antisymm (hupper d)
  have hl := observability_beta_kernel_lower q (genericAffineSquare K n m)
    (genericAffineRows K n m) (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m) d
  rwa [corank_one_observability_beta_dimension_identity q d _ _ (by omega) hn] at hl

end FD56
