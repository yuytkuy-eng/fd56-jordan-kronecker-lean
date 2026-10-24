/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.ObservabilityBetaCoefficients
import FD56.Hilbert.GenericKernelExtension
import FD56.Hilbert.GenericDepthThreeRightInverse

/-! Arbitrary-field witnesses control the generic second auxiliary relation. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K L m n : Type*} [Field K] [Field L]
  [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem generic_observability_beta_kernel_le_field_witness
    (q : ℕ) (σ : K →+* L) (M : Matrix n n L[X]) (P : Matrix m n L[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) (d : ℕ) :
    Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (boundedObservabilityBetaKernel q (genericAffineSquare K n m) (genericAffineRows K n m) d) ≤
      Module.finrank L (boundedObservabilityBetaKernel q M P d) := by
  let ψ := affinePairFieldSpecialization σ M P
  let φ := algebraMap (MvPolynomial (MatrixParameters n m ⊕ MatrixParameters n m) K)
    (AffineCoefficientField K (MatrixParameters n m))
  let A := observabilityBetaCoefficientMatrix q (universalAffineSquare K n m)
    (universalAffineRows K n m) d
  have he : A.map ψ = observabilityBetaCoefficientMatrix q M P d := by
    dsimp only [A,ψ]
    rw [← observabilityBetaCoefficientMatrix_map,
      universalAffineSquare_field_specialization σ M P hM,
      universalAffineRows_field_specialization σ M P hP]
  have hg : A.map φ = observabilityBetaCoefficientMatrix q
      (genericAffineSquare K n m) (genericAffineRows K n m) d := by
    dsimp only [A,φ]
    rw [← observabilityBetaCoefficientMatrix_map,
      universalAffineSquare_generic,universalAffineRows_generic]
  have hh := matrix_kernel_finrank_le_of_field_specialization ψ φ
    (IsFractionRing.injective _ _) A
  rw [he,hg,observability_beta_coefficient_kernel_finrank q _ _
    (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m) d,
    observability_beta_coefficient_kernel_finrank q M P hM hP d] at hh
  exact hh

theorem generic_depth_three_beta_hilbert_of_field_witness
    (σ : K →+* L) (M : Matrix n n L[X]) (P : Matrix m n L[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) (d : ℕ)
    (hw : Module.finrank L (boundedObservabilityBetaKernel 3 M P d) ≤
      Fintype.card m*(4*d+10)-Fintype.card n*(d+5)) :
    Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (boundedObservabilityBetaKernel 3 (genericAffineSquare K n m) (genericAffineRows K n m) d) =
      Fintype.card m*(4*d+10)-Fintype.card n*(d+5) := by
  exact le_antisymm
    ((generic_observability_beta_kernel_le_field_witness 3 σ M P hM hP d).trans hw)
    (depth_three_beta_kernel_lower _ _ (genericAffineSquare_degree K n m)
      (genericAffineRows_degree K n m) d)

theorem depth_three_beta_dimension_identity (n m d : ℕ)
    (hmn : 3*m ≤ n) (hnm : n ≤ 4*m) :
    m*(4*d+10)-n*(d+5) =
      (m-(n-3*m))*(d+1)-(6*m+4*(n-3*m)) := by
  have hn : n = 3*m+(n-3*m) := by omega
  have hm : m = (m-(n-3*m))+(n-3*m) := by omega
  have hn' := congrArg (fun x : ℕ => x*(d+5)) hn
  have hm' := congrArg (fun x : ℕ => x*(d+1)) hm
  have he : m*(4*d+10)+(6*m+4*(n-3*m)) =
      n*(d+5)+(m-(n-3*m))*(d+1) := by nlinarith only [hn',hm']
  omega

theorem generic_depth_three_actual_beta_finrank {r : Type*} [Fintype r]
    (hmn : 3*Fintype.card m < Fintype.card n)
    (B : Basis r (AffineCoefficientField K (MatrixParameters n m))[X]
      (LinearMap.ker (Matrix.toLin' (observabilityMatrix
        (genericAffineSquare K n m) (genericAffineRows K n m) 3)))) (d : ℕ) :
    Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (boundedObservabilityBetaKernel 3 (genericAffineSquare K n m)
        (genericAffineRows K n m) d) =
    Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (polynomialKernelAtDegree
        (genericAffineRows K n m * (genericAffineSquare K n m)^3 *
          polynomialKernelBasisMatrix (observabilityMatrix
            (genericAffineSquare K n m) (genericAffineRows K n m) 3) B).transpose d) := by
  obtain ⟨R,_,hR⟩ := generic_actual_depth_three_stack_right_inverse (K := K) hmn
  exact observability_beta_kernel_finrank 3 _ _ B R hR
    (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m)
    (generic_actual_depth_three_stack_leading_injective (K := K) hmn) d

end FD56
