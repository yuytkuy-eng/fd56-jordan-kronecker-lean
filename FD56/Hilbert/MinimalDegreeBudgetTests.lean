/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthThreeBetaCriterion

/-! Finite tests for balanced minimal degrees when the count and total degree are known. -/

noncomputable section
namespace FD56
open Matrix Polynomial

private theorem truncated_list_sum_bounds (xs : List ℕ) (d : ℕ) :
    xs.length*d-xs.sum ≤ (xs.map (fun e => d-e)).sum ∧
      (xs.map (fun e => d-e)).sum ≤ xs.length*d := by
  induction xs with
  | nil => simp
  | cons e xs ih =>
    simp only [List.length_cons,List.sum_cons,List.map_cons]
    have h1 : xs.length*d ≤ (xs.map (fun e => d-e)).sum+xs.sum := by omega
    have h2 : d ≤ (d-e)+e := by omega
    have h3 : (d-e) ≤ d := by omega
    constructor
    · apply Nat.sub_le_of_le_add
      nlinarith
    · nlinarith

private theorem truncated_list_growth (xs : List ℕ) (d : ℕ) :
    (xs.map (fun e => d+1-e)).sum ≤ (xs.map (fun e => d-e)).sum+xs.length := by
  induction xs with
  | nil => simp
  | cons e xs ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    have h : d+1-e ≤ d-e+1 := by omega
    omega

theorem minimal_degrees_balanced_of_budget_tests
    {K x y : Type*} [Field K] [Fintype y] [DecidableEq y]
    (A : Matrix x y K[X]) (xs : List ℕ) (hmin : HasMinimalKernelDegrees A xs)
    (D a b : ℕ) (hD : 0<D) (hs : 0<a+b)
    (hlen : xs.length=a+b) (hsum : xs.sum=D*(a+b)+b)
    (hzero : Module.finrank K (polynomialKernelAtDegree A (D-1))=0)
    (hcritical : Module.finrank K (polynomialKernelAtDegree A D)≤a) :
    HasMinimalKernelDegrees A (balancedDegreeList (D*(a+b)+b) (a+b)) := by
  apply hasMinimalKernelDegrees_balanced_of_two_tests A D a b hD hs
  · intro d
    rw [(hasMinimalKernelDegrees_iff_hilbert A xs).mp hmin d]
    simpa only [hlen,hsum] using (truncated_list_sum_bounds xs (d+1)).1
  · intro d
    rw [(hasMinimalKernelDegrees_iff_hilbert A xs).mp hmin d]
    simpa only [hlen] using (truncated_list_sum_bounds xs (d+1)).2
  · exact hzero
  · exact hcritical

theorem minimal_degrees_uniform_of_budget_test
    {K x y : Type*} [Field K] [Fintype y] [DecidableEq y]
    (A : Matrix x y K[X]) (xs : List ℕ) (hmin : HasMinimalKernelDegrees A xs)
    (D r : ℕ) (hD : 0<D) (hr : 0<r)
    (hlen : xs.length=r) (hsum : xs.sum=D*r)
    (hzero : Module.finrank K (polynomialKernelAtDegree A (D-1))=0) :
    HasMinimalKernelDegrees A (List.replicate r D) := by
  have hh := (hasMinimalKernelDegrees_iff_hilbert A xs).mp hmin
  have hz : (xs.map (fun e => D-e)).sum=0 := by
    rw [hh (D-1)] at hzero
    simpa only [show D-1+1=D by omega] using hzero
  have hc : Module.finrank K (polynomialKernelAtDegree A D)≤r := by
    rw [hh D]
    simpa only [hz,hlen,Nat.zero_add] using truncated_list_growth xs D
  have hb := minimal_degrees_balanced_of_budget_tests A xs hmin D r 0 hD
    (by omega) (by simpa using hlen) (by simpa using hsum) hzero hc
  simpa [balancedDegreeList,Nat.ne_of_gt hr] using hb

end FD56
