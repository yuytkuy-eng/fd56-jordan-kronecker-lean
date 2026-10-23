/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericDepthTwoBeta
import FD56.Hilbert.GenericDepthTwoRank
import FD56.Hilbert.DepthTwoGL
import FD56.Hilbert.ConvolutionDegrees

/-! The complete generic GL polynomial minimal-degree list for 2m < n < 3m. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K m n : Type*} [Field K] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

theorem generic_depth_two_gl_minimal_degrees
    (hmn : 2*Fintype.card m < Fintype.card n)
    (hnm : Fintype.card n < 3*Fintype.card m) :
    HasMinimalKernelDegrees
      (glEquationMatrix (genericAffineSquare K n m) (genericAffineRows K n m))
      ((degreeConvolution
        (balancedDegreeList (3*Fintype.card m) (Fintype.card n-2*Fintype.card m))
        (balancedDegreeList (3*Fintype.card m+3*(Fintype.card n-2*Fintype.card m))
          (Fintype.card m-(Fintype.card n-2*Fintype.card m)))).map (fun e => e+1)) := by
  obtain ⟨r,Bv,a,hV,hVL,ha⟩ := generic_actual_depth_two_stack_minimal_degrees (K := K) hmn
  obtain ⟨s,Bt,b,hT,hTL,hb⟩ := generic_depth_two_auxiliary_minimal_degrees Bv hmn hnm
  obtain ⟨R,_,hR⟩ := generic_actual_depth_two_stack_right_inverse (K := K) hmn
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [depthTwo_gl_kernel_hilbert_of_bases _ _ Bv Bt R hR
    (generic_depth_two_kernel_transfer_injective hmn.le hnm.le Bv) a b
    (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m)
    hV hT hVL hTL (generic_actual_depth_two_stack_leading_injective hmn) d]
  simpa only [degreeConvolution,List.map_flatMap,List.map_map,Function.comp_def,Nat.add_assoc]
    using sum_pairs_of_permuted_degrees a b _ _ ha hb (fun x y => d+1-(x+y+2))

end FD56
