/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthThreeBetaCriterion

/-! One coefficient test suffices when the expected auxiliary degrees coincide. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K m n : Type*} [Field K] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

theorem generic_depth_three_beta_degrees_of_single_test
    (hmn : 3*Fintype.card m < Fintype.card n)
    (hnm : Fintype.card n < 4*Fintype.card m)
    (B : Basis (Fin (Fintype.card n-3*Fintype.card m))
      (AffineCoefficientField K (MatrixParameters n m))[X]
      (LinearMap.ker (Matrix.toLin' (observabilityMatrix
        (genericAffineSquare K n m) (genericAffineRows K n m) 3))))
    (D : ℕ) (hD : 0<D)
    (hweight : D*(Fintype.card m-(Fintype.card n-3*Fintype.card m))=
      6*Fintype.card m+4*(Fintype.card n-3*Fintype.card m))
    (hzero : Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (boundedObservabilityBetaKernel 3 (genericAffineSquare K n m)
        (genericAffineRows K n m) (D-1))=0) :
    HasMinimalKernelDegrees
      (genericAffineRows K n m * (genericAffineSquare K n m)^3 *
        polynomialKernelBasisMatrix (observabilityMatrix
          (genericAffineSquare K n m) (genericAffineRows K n m) 3) B).transpose
      (balancedDegreeList (6*Fintype.card m+4*(Fintype.card n-3*Fintype.card m))
        (Fintype.card m-(Fintype.card n-3*Fintype.card m))) := by
  apply generic_depth_three_beta_degrees_of_two_tests hmn hnm B D
    (Fintype.card m-(Fintype.card n-3*Fintype.card m)) 0 hD (by omega)
    (by simpa only [Nat.add_zero] using hweight) hzero
  have hh := polynomial_left_kernel_growth_bound _
    (terminal_kernel_transfer_eval_injective 3 _ _ B 0
      (generic_terminal_observability_zero_injective 3 hmn.le hnm.le)) (D-1)
  rw [show D-1+1=D by omega,
    ← generic_depth_three_actual_beta_finrank hmn B D,
    ← generic_depth_three_actual_beta_finrank hmn B (D-1),hzero] at hh
  simpa only [Fintype.card_fin,Nat.zero_add] using hh

theorem generic_depth_three_beta_degrees_of_single_field_witness
    {L : Type*} [Field L] (σ : K →+* L)
    (M : Matrix n n L[X]) (P : Matrix m n L[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hmn : 3*Fintype.card m < Fintype.card n)
    (hnm : Fintype.card n < 4*Fintype.card m)
    (B : Basis (Fin (Fintype.card n-3*Fintype.card m))
      (AffineCoefficientField K (MatrixParameters n m))[X]
      (LinearMap.ker (Matrix.toLin' (observabilityMatrix
        (genericAffineSquare K n m) (genericAffineRows K n m) 3))))
    (D : ℕ) (hD : 0<D)
    (hweight : D*(Fintype.card m-(Fintype.card n-3*Fintype.card m))=
      6*Fintype.card m+4*(Fintype.card n-3*Fintype.card m))
    (hzero : Module.finrank L (LinearMap.ker
      (Matrix.toLin' (observabilityBetaCoefficientMatrix 3 M P (D-1))))=0) :
    HasMinimalKernelDegrees
      (genericAffineRows K n m * (genericAffineSquare K n m)^3 *
        polynomialKernelBasisMatrix (observabilityMatrix
          (genericAffineSquare K n m) (genericAffineRows K n m) 3) B).transpose
      (balancedDegreeList (6*Fintype.card m+4*(Fintype.card n-3*Fintype.card m))
        (Fintype.card m-(Fintype.card n-3*Fintype.card m))) := by
  apply generic_depth_three_beta_degrees_of_single_test hmn hnm B D hD hweight
  have hh := generic_observability_beta_kernel_le_field_witness 3 σ M P hM hP (D-1)
  rw [observability_beta_coefficient_kernel_finrank 3 M P hM hP (D-1)] at hzero
  rw [hzero] at hh
  exact Nat.eq_zero_of_le_zero hh

end FD56
