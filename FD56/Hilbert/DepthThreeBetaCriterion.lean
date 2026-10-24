/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericObservabilityBetaTransfer
import FD56.Hilbert.ObservabilityBetaGrowth
import FD56.Hilbert.AdjacentCriterion
import FD56.Hilbert.AdjacentDegrees

/-! Two bounded rank tests suffice for the third auxiliary degree list. -/

noncomputable section
namespace FD56
open Matrix Polynomial

theorem hasMinimalKernelDegrees_balanced_of_two_tests
    {K x y : Type*} [Field K] [Fintype y] [DecidableEq y]
    (F : Matrix x y K[X]) (D a b : ℕ) (hD : 0<D) (hs : 0<a+b)
    (hlower : ∀ d, (a+b)*(d+1)-(D*(a+b)+b) ≤
      Module.finrank K (polynomialKernelAtDegree F d))
    (hupper : ∀ d, Module.finrank K (polynomialKernelAtDegree F d) ≤ (a+b)*(d+1))
    (hzero : Module.finrank K (polynomialKernelAtDegree F (D-1))=0)
    (hcritical : Module.finrank K (polynomialKernelAtDegree F D)≤a) :
    HasMinimalKernelDegrees F (balancedDegreeList (D*(a+b)+b) (a+b)) := by
  apply hasMinimalKernelDegrees_balanced_of_adjacent F a b D hs
  apply hasMinimalKernelDegrees_adjacent_of_bounds F D a b 0 hD hzero
  · have hh := hlower D
    have he : (a+b)*(D+1)-(D*(a+b)+b)=a := by
      have : (a+b)*(D+1)=(D*(a+b)+b)+a := by ring
      rw [this,Nat.add_sub_cancel_left]
    rw [he] at hh
    exact le_antisymm hcritical hh
  · have hh := hlower (D+2)
    have he : (a+b)*(D+2+1)-(D*(a+b)+b)=3*a+2*b := by
      have : (a+b)*(D+2+1)=(D*(a+b)+b)+(3*a+2*b) := by ring
      rw [this,Nat.add_sub_cancel_left]
    rwa [he] at hh
  · intro d
    simpa only [Nat.add_zero] using hupper d

variable {K m n : Type*} [Field K] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

theorem generic_depth_three_beta_degrees_of_two_tests
    (hmn : 3*Fintype.card m < Fintype.card n)
    (hnm : Fintype.card n < 4*Fintype.card m)
    (B : Basis (Fin (Fintype.card n-3*Fintype.card m))
      (AffineCoefficientField K (MatrixParameters n m))[X]
      (LinearMap.ker (Matrix.toLin' (observabilityMatrix
        (genericAffineSquare K n m) (genericAffineRows K n m) 3))))
    (D a b : ℕ) (hD : 0<D)
    (hs : a+b=Fintype.card m-(Fintype.card n-3*Fintype.card m))
    (hweight : D*(a+b)+b=6*Fintype.card m+4*(Fintype.card n-3*Fintype.card m))
    (hzero : Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (boundedObservabilityBetaKernel 3 (genericAffineSquare K n m)
        (genericAffineRows K n m) (D-1))=0)
    (hcritical : Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (boundedObservabilityBetaKernel 3 (genericAffineSquare K n m)
        (genericAffineRows K n m) D)≤a) :
    HasMinimalKernelDegrees
      (genericAffineRows K n m * (genericAffineSquare K n m)^3 *
        polynomialKernelBasisMatrix (observabilityMatrix
          (genericAffineSquare K n m) (genericAffineRows K n m) 3) B).transpose
      (balancedDegreeList (6*Fintype.card m+4*(Fintype.card n-3*Fintype.card m))
        (Fintype.card m-(Fintype.card n-3*Fintype.card m))) := by
  rw [← hs,← hweight]
  apply hasMinimalKernelDegrees_balanced_of_two_tests _ D a b hD (by omega)
  · intro d
    rw [← generic_depth_three_actual_beta_finrank hmn B d,hweight,hs,
      ← depth_three_beta_dimension_identity _ _ d hmn.le hnm.le]
    exact depth_three_beta_kernel_lower _ _ (genericAffineSquare_degree K n m)
      (genericAffineRows_degree K n m) d
  · intro d
    have hh := generic_observability_beta_linear_bound 3 hmn.le hnm.le B d
    simpa only [Fintype.card_fin,hs] using hh
  · rwa [← generic_depth_three_actual_beta_finrank hmn B (D-1)]
  · rwa [← generic_depth_three_actual_beta_finrank hmn B D]

theorem generic_depth_three_beta_degrees_of_two_field_witnesses
    {L : Type*} [Field L] (σ : K →+* L)
    (M₀ M₁ : Matrix n n L[X]) (P₀ P₁ : Matrix m n L[X])
    (hM₀ : DegreeBound M₀ 1) (hM₁ : DegreeBound M₁ 1)
    (hP₀ : DegreeBound P₀ 1) (hP₁ : DegreeBound P₁ 1)
    (hmn : 3*Fintype.card m < Fintype.card n)
    (hnm : Fintype.card n < 4*Fintype.card m)
    (B : Basis (Fin (Fintype.card n-3*Fintype.card m))
      (AffineCoefficientField K (MatrixParameters n m))[X]
      (LinearMap.ker (Matrix.toLin' (observabilityMatrix
        (genericAffineSquare K n m) (genericAffineRows K n m) 3))))
    (D a b : ℕ) (hD : 0<D)
    (hs : a+b=Fintype.card m-(Fintype.card n-3*Fintype.card m))
    (hweight : D*(a+b)+b=6*Fintype.card m+4*(Fintype.card n-3*Fintype.card m))
    (hzero : Module.finrank L (LinearMap.ker
      (Matrix.toLin' (observabilityBetaCoefficientMatrix 3 M₀ P₀ (D-1))))=0)
    (hcritical : Module.finrank L (LinearMap.ker
      (Matrix.toLin' (observabilityBetaCoefficientMatrix 3 M₁ P₁ D)))≤a) :
    HasMinimalKernelDegrees
      (genericAffineRows K n m * (genericAffineSquare K n m)^3 *
        polynomialKernelBasisMatrix (observabilityMatrix
          (genericAffineSquare K n m) (genericAffineRows K n m) 3) B).transpose
      (balancedDegreeList (6*Fintype.card m+4*(Fintype.card n-3*Fintype.card m))
        (Fintype.card m-(Fintype.card n-3*Fintype.card m))) := by
  apply generic_depth_three_beta_degrees_of_two_tests hmn hnm B D a b hD hs hweight
  · have hh := generic_observability_beta_kernel_le_field_witness 3 σ M₀ P₀ hM₀ hP₀ (D-1)
    rw [observability_beta_coefficient_kernel_finrank 3 M₀ P₀ hM₀ hP₀ (D-1)] at hzero
    rw [hzero] at hh
    exact Nat.eq_zero_of_le_zero hh
  · have hh := generic_observability_beta_kernel_le_field_witness 3 σ M₁ P₁ hM₁ hP₁ D
    rw [observability_beta_coefficient_kernel_finrank 3 M₁ P₁ hM₁ hP₁ D] at hcritical
    exact hh.trans hcritical

end FD56
