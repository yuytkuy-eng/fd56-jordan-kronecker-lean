/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthTwoBetaWitness
import FD56.Hilbert.GenericDepthTwoBetaTransfer
import FD56.Hilbert.GenericActualDepthTwoStack

/-! The second generic auxiliary degree list throughout the depth-two range. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K m n : Type*} [Field K] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

theorem generic_depth_two_beta_hilbert
    (hmn : 2*Fintype.card m < Fintype.card n)
    (hnm : Fintype.card n < 3*Fintype.card m) (d : ℕ) :
    Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (boundedDepthTwoBetaKernel (genericAffineSquare K n m) (genericAffineRows K n m) d) =
      Fintype.card m*(3*d+6)-Fintype.card n*(d+4) := by
  obtain ⟨M,P,hM,hP,hH⟩ := exists_depth_two_beta_witness (K := K) hmn hnm
  let S := MvPolynomial (PrescribedMatrixParameters n (depthTwoRowDegree (m := m))) K
  let F₀ := DepthTwoStackField K n m
  let σ : K →+* DepthTwoBetaWitnessField K n m :=
    (algebraMap F₀[X] (DepthTwoBetaWitnessField K n m)).comp
      (Polynomial.C.comp ((algebraMap S F₀).comp MvPolynomial.C))
  exact generic_depth_two_beta_hilbert_of_field_witness σ M P hM hP d (hH d)

theorem generic_depth_two_auxiliary_minimal_degrees
    {r : Type*} [Fintype r]
    (B : Basis r (AffineCoefficientField K (MatrixParameters n m))[X]
      (LinearMap.ker (Matrix.toLin' (depthTwoStack (genericAffineRows K n m)
        (genericAffineRows K n m*genericAffineSquare K n m)))))
    (hmn : 2*Fintype.card m < Fintype.card n)
    (hnm : Fintype.card n < 3*Fintype.card m) :
    HasMinimalKernelDegrees
      (genericAffineRows K n m*genericAffineSquare K n m*genericAffineSquare K n m*
        polynomialKernelBasisMatrix _ B).transpose
      (balancedDegreeList (3*Fintype.card m+3*(Fintype.card n-2*Fintype.card m))
        (Fintype.card m-(Fintype.card n-2*Fintype.card m))) := by
  obtain ⟨R,_,hR⟩ := generic_actual_depth_two_stack_right_inverse (K := K) hmn
  have hlead := generic_actual_depth_two_stack_leading_injective (K := K) hmn
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [← depthTwo_beta_kernel_finrank _ _ B R hR (genericAffineSquare_degree K n m)
    (genericAffineRows_degree K n m) hlead d,
    generic_depth_two_beta_hilbert hmn hnm d,
    balancedDegreeList_hilbert _ _ d (by omega)]
  exact depthTwo_beta_dimension_identity _ _ d hmn.le hnm.le

end FD56
