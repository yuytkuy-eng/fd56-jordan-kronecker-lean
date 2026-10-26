/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.ConvolutionDegrees
import FD56.Hilbert.BalancedDegrees

/-! Exact Kronecker dimension budgets for the two established low-depth
generic GL degree lists. The divisible boundary is excluded. -/

namespace FD56

theorem nat_list_affine_sum (xs : List ℕ) (a b : ℕ) :
    (xs.map (fun x => a*x+b)).sum = a*xs.sum + b*xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    ring

theorem degreeConvolution_block_dimension (alpha beta : List ℕ) (shift : ℕ) :
    ((degreeConvolution alpha beta).map (fun e => 2*(e+shift)+1)).sum =
      2*beta.length*alpha.sum + 2*alpha.length*beta.sum +
        (2*shift+3)*(alpha.length*beta.length) := by
  have hinner (a : ℕ) : (beta.map (fun b => 2*(a+b+1+shift)+1)).sum =
      2*beta.sum + (2*a+2*shift+3)*beta.length := by
    have hf : (fun b : ℕ => 2*(a+b+1+shift)+1) = fun b => 2*b+(2*a+2*shift+3) := by
      funext b
      ring
    rw [hf, nat_list_affine_sum]
  induction alpha with
  | nil => simp [degreeConvolution]
  | cons a alpha ih =>
    rw [show degreeConvolution (a::alpha) beta =
      beta.map (fun b => a+b+1) ++ degreeConvolution alpha beta by rfl]
    simp only [List.map_append, List.sum_append, List.map_map, Function.comp_def,
      List.sum_cons, List.length_cons, ih]
    rw [hinner]
    ring

theorem middle_gl_dimension_budget (m n : ℕ) (hmn : m < n) (hnm : n < 2*m) :
    ((degreeConvolution (balancedDegreeList m (n-m))
      (balancedDegreeList (m+2*(n-m)) (m-(n-m)))).map (fun e => 2*e+1)).sum = n*(n+m) := by
  have ha : 0 < n-m := by omega
  have hb : 0 < m-(n-m) := by omega
  have h := degreeConvolution_block_dimension
    (balancedDegreeList m (n-m)) (balancedDegreeList (m+2*(n-m)) (m-(n-m))) 0
  simp only [Nat.add_zero, Nat.mul_zero, Nat.zero_add] at h
  rw [h, balancedDegreeList_length _ _ ha, balancedDegreeList_length _ _ hb,
    balancedDegreeList_sum _ _ ha, balancedDegreeList_sum _ _ hb]
  have hn : n = m+(n-m) := by omega
  have hm : m = (n-m)+(m-(n-m)) := by omega
  nlinarith

theorem depth_two_gl_dimension_budget (m n : ℕ) (hmn : 2*m < n) (hnm : n < 3*m) :
    (((degreeConvolution (balancedDegreeList (3*m) (n-2*m))
      (balancedDegreeList (3*m+3*(n-2*m)) (m-(n-2*m)))).map (fun e => e+1)).map
        (fun e => 2*e+1)).sum = n*(n+m) := by
  have ha : 0 < n-2*m := by omega
  have hb : 0 < m-(n-2*m) := by omega
  rw [List.map_map]
  change ((degreeConvolution _ _).map (fun e => 2*(e+1)+1)).sum = _
  rw [degreeConvolution_block_dimension,
    balancedDegreeList_length _ _ ha, balancedDegreeList_length _ _ hb,
    balancedDegreeList_sum _ _ ha, balancedDegreeList_sum _ _ hb]
  have hn : n = 2*m+(n-2*m) := by omega
  have hm : m = (n-2*m)+(m-(n-2*m)) := by omega
  nlinarith

end FD56
