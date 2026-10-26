/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.ObservabilityBetaCoefficients

/-! Dimension lower bounds for bounded auxiliary relations at every depth. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

theorem observability_beta_coefficient_count (q d : ℕ) :
    (d+1) + (∑ i : Fin q, (d+q-i.val+1)) +
      (∑ i : Fin (q+1), (i.val+1)) = (q+1)*(d+q+2) := by
  have he : (d+1) + (∑ i : Fin q, (d+q-i.val+1)) =
      ∑ i : Fin (q+1), (d+q-i.val+1) := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    omega
  rw [he, ← Finset.sum_add_distrib]
  have ht (i : Fin (q+1)) : d+q-i.val+1+(i.val+1)=d+q+2 := by
    have := i.isLt
    omega
  simp only [ht, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

variable {K m n : Type*} [Field K] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

theorem observability_beta_kernel_lower (q : ℕ)
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) (d : ℕ) :
    Fintype.card m*((d+1)+(∑ i : Fin q, (d+q-i.val+1))) -
      Fintype.card n*(d+q+2) ≤
        Module.finrank K (boundedObservabilityBetaKernel q M P d) := by
  let T := Matrix.toLin' (observabilityBetaCoefficientMatrix q M P d)
  have hh := T.finrank_range_add_finrank_ker
  have hl := Submodule.finrank_le (LinearMap.range T)
  rw [observability_beta_coefficient_kernel_finrank q M P hM hP d] at hh
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sigma, Fintype.card_fin,
    observabilityBetaDegrees, observabilityBetaCoefficientDegree, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, Fintype.sum_prod_type, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, ← Finset.mul_sum] at hh hl
  change Module.finrank K (LinearMap.range T) +
    Module.finrank K (boundedObservabilityBetaKernel q M P d) = _ at hh
  rw [Nat.mul_add]
  omega

theorem corank_one_observability_beta_dimension_identity (q d m n : ℕ)
    (hm : 1 ≤ m) (hn : n+1=(q+1)*m) :
    m*((d+1)+(∑ i : Fin q, (d+q-i.val+1))) - n*(d+q+2) =
      d+1-(m*(∑ i : Fin (q+1), (i.val+1))-(q+1)) := by
  have hc := observability_beta_coefficient_count q d
  have hs : q+1 ≤ ∑ i : Fin (q+1), (i.val+1) := by
    calc
      q+1 = ∑ _i : Fin (q+1), 1 := by simp
      _ ≤ ∑ i : Fin (q+1), (i.val+1) := Finset.sum_le_sum (by intros; omega)
  have hms : q+1 ≤ m*(∑ i : Fin (q+1), (i.val+1)) := by nlinarith
  have hD := Nat.sub_add_cancel hms
  have he : m*((d+1)+(∑ i : Fin q, (d+q-i.val+1))) +
      (m*(∑ i : Fin (q+1), (i.val+1))-(q+1)) = n*(d+q+2)+(d+1) := by
    nlinarith
  omega

end FD56
