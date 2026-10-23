/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthTwoBetaCoefficients
import FD56.Hilbert.GenericKernelExtension

/-! Arbitrary-field witnesses control the generic second auxiliary relation. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K L m n : Type*} [Field K] [Field L]
  [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem generic_depth_two_beta_kernel_le_field_witness
    (σ : K →+* L) (M : Matrix n n L[X]) (P : Matrix m n L[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) (d : ℕ) :
    Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (boundedDepthTwoBetaKernel (genericAffineSquare K n m) (genericAffineRows K n m) d) ≤
      Module.finrank L (boundedDepthTwoBetaKernel M P d) := by
  let ψ := affinePairFieldSpecialization σ M P
  let φ := algebraMap (MvPolynomial (MatrixParameters n m ⊕ MatrixParameters n m) K)
    (AffineCoefficientField K (MatrixParameters n m))
  let A := depthTwoBetaCoefficientMatrix (universalAffineSquare K n m)
    (universalAffineRows K n m) d
  have he : A.map ψ = depthTwoBetaCoefficientMatrix M P d := by
    dsimp only [A,ψ]
    rw [← depthTwoBetaCoefficientMatrix_map,
      universalAffineSquare_field_specialization σ M P hM,
      universalAffineRows_field_specialization σ M P hP]
  have hg : A.map φ = depthTwoBetaCoefficientMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m) d := by
    dsimp only [A,φ]
    rw [← depthTwoBetaCoefficientMatrix_map,
      universalAffineSquare_generic,universalAffineRows_generic]
  have hh := matrix_kernel_finrank_le_of_field_specialization ψ φ
    (IsFractionRing.injective _ _) A
  rw [he,hg,depthTwo_beta_coefficient_kernel_finrank _ _
    (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m) d,
    depthTwo_beta_coefficient_kernel_finrank M P hM hP d] at hh
  exact hh

theorem generic_depth_two_beta_hilbert_of_field_witness
    (σ : K →+* L) (M : Matrix n n L[X]) (P : Matrix m n L[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) (d : ℕ)
    (hw : Module.finrank L (boundedDepthTwoBetaKernel M P d) ≤
      Fintype.card m*(3*d+6)-Fintype.card n*(d+4)) :
    Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (boundedDepthTwoBetaKernel (genericAffineSquare K n m) (genericAffineRows K n m) d) =
      Fintype.card m*(3*d+6)-Fintype.card n*(d+4) := by
  exact le_antisymm
    ((generic_depth_two_beta_kernel_le_field_witness σ M P hM hP d).trans hw)
    (depthTwo_beta_kernel_lower _ _ (genericAffineSquare_degree K n m)
      (genericAffineRows_degree K n m) d)

theorem depthTwo_beta_dimension_identity (n m d : ℕ)
    (hmn : 2*m ≤ n) (hnm : n ≤ 3*m) :
    m*(3*d+6)-n*(d+4) =
      (m-(n-2*m))*(d+1)-(3*m+3*(n-2*m)) := by
  have hn : n = 2*m+(n-2*m) := by omega
  have hm : m = (m-(n-2*m))+(n-2*m) := by omega
  have hn' := congrArg (fun x : ℕ => x*(d+4)) hn
  have hm' := congrArg (fun x : ℕ => x*(d+1)) hm
  have he : m*(3*d+6)+(3*m+3*(n-2*m)) =
      n*(d+4)+(m-(n-2*m))*(d+1) := by nlinarith only [hn',hm']
  omega

end FD56
