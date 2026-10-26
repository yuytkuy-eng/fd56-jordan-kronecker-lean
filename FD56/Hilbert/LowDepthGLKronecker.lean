/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MixedGLKronecker
import FD56.Hilbert.GenericMiddle
import FD56.Hilbert.GenericDepthTwoGL
import FD56.Hilbert.LowDepthGLDimension

/-! Complete constant-congruence Kronecker decompositions of the generic GL
Kirillov pencil in the strict ranges m < n < 2m and 2m < n < 3m. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem generic_middle_gl_kronecker_decomposition
    (hmn : Fintype.card m < Fintype.card n)
    (hnm : Fintype.card n < 2*Fintype.card m) :
    HasKroneckerDecomposition (glKirillovMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m))
      (degreeConvolution
        (balancedDegreeList (Fintype.card m) (Fintype.card n-Fintype.card m))
        (balancedDegreeList (Fintype.card m+2*(Fintype.card n-Fintype.card m))
          (Fintype.card m-(Fintype.card n-Fintype.card m)))) := by
  apply glKirillovMatrix_kronecker _ _ _
    (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m)
    (generic_middle_gl_minimal_degrees hmn hnm)
  rw [middle_gl_dimension_budget _ _ hmn hnm]
  simp only [SLInput, Fintype.card_sum, Fintype.card_prod]
  ring

theorem generic_depth_two_gl_kronecker_decomposition
    (hmn : 2*Fintype.card m < Fintype.card n)
    (hnm : Fintype.card n < 3*Fintype.card m) :
    HasKroneckerDecomposition (glKirillovMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m))
      ((degreeConvolution
        (balancedDegreeList (3*Fintype.card m) (Fintype.card n-2*Fintype.card m))
        (balancedDegreeList (3*Fintype.card m+3*(Fintype.card n-2*Fintype.card m))
          (Fintype.card m-(Fintype.card n-2*Fintype.card m)))).map (fun e => e+1)) := by
  apply glKirillovMatrix_kronecker _ _ _
    (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m)
    (generic_depth_two_gl_minimal_degrees hmn hnm)
  rw [depth_two_gl_dimension_budget _ _ hmn hnm]
  simp only [SLInput, Fintype.card_sum, Fintype.card_prod]
  ring

end FD56
