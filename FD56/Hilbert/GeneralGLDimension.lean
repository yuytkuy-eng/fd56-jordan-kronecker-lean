/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.LowDepthGLDimension

/-! The full Kronecker dimension budget from arbitrary-depth auxiliary totals.
No balancing assumption is needed for the first identity. -/

namespace FD56

theorem observability_gl_dimension_budget (m n q : ℕ) (alpha beta : List ℕ)
    (hlen : alpha.length + beta.length = m)
    (hn : n = (q+1)*m + alpha.length)
    (ha : 2*alpha.sum = m*(q+1)*(q+2))
    (hb : beta.sum = alpha.sum + (q+2)*alpha.length) :
    (((degreeConvolution alpha beta).map (fun e => e+q)).map
      (fun e => 2*e+1)).sum = n*(n+m) := by
  rw [List.map_map]
  change ((degreeConvolution alpha beta).map (fun e => 2*(e+q)+1)).sum = _
  rw [degreeConvolution_block_dimension, hb, hn]
  calc
    2*beta.length*alpha.sum + 2*alpha.length*(alpha.sum+(q+2)*alpha.length) +
        (2*q+3)*(alpha.length*beta.length) =
      (alpha.length+beta.length)*(2*alpha.sum) +
        2*(q+2)*alpha.length^2 + (2*q+3)*alpha.length*beta.length := by ring
    _ = m*(m*(q+1)*(q+2)) +
        2*(q+2)*alpha.length^2 + (2*q+3)*alpha.length*beta.length := by rw [hlen,ha]
    _ = ((q+1)*m+alpha.length)*((q+1)*m+alpha.length+m) := by
      rw [← hlen]
      ring

theorem balanced_observability_gl_dimension_budget (m n q S : ℕ)
    (hlo : (q+1)*m < n) (hhi : n < (q+2)*m)
    (hS : 2*S = m*(q+1)*(q+2)) :
    (((degreeConvolution (balancedDegreeList S (n-(q+1)*m))
      (balancedDegreeList (S+(q+2)*(n-(q+1)*m)) (m-(n-(q+1)*m)))).map
        (fun e => e+q)).map (fun e => 2*e+1)).sum = n*(n+m) := by
  have ha : 0 < n-(q+1)*m := by omega
  have hhi' : n < (q+1)*m+m := by nlinarith
  have hb : 0 < m-(n-(q+1)*m) := by omega
  apply observability_gl_dimension_budget m n q
  · rw [balancedDegreeList_length _ _ ha,balancedDegreeList_length _ _ hb]
    omega
  · rw [balancedDegreeList_length _ _ ha]
    omega
  · rwa [balancedDegreeList_sum _ _ ha]
  · rw [balancedDegreeList_sum _ _ ha,balancedDegreeList_sum _ _ hb,
      balancedDegreeList_length _ _ ha]

end FD56
