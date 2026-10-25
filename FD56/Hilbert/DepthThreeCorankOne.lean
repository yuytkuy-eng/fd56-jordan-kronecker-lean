/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GenericObservabilityCoprime
import FD56.LinearAlgebra.CorankOneKernelGenerator
import FD56.Hilbert.CorankOneObservabilityLeading
import FD56.Hilbert.ObservabilityBetaCofactorBound
import FD56.Hilbert.DepthThreeBetaSingleTest

/-! The corank-one third-depth auxiliary degree over every field. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem generic_corank_one_depth_three_beta_zero
    (hm : 2 ≤ Fintype.card m) (hn : Fintype.card n + 1 = 4 * Fintype.card m) :
    Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (boundedObservabilityBetaKernel 3 (genericAffineSquare K n m)
        (genericAffineRows K n m) (10 * Fintype.card m - 5)) = 0 := by
  obtain ⟨j, e, hdeg, hne⟩ := generic_corank_one_terminal_minor_exact_degree (K := K) hm hn
  obtain ⟨c, hc, _, hgen⟩ := corank_one_kernel_generator
    (observabilityMatrix (genericAffineSquare K n m) (genericAffineRows K n m) 4)
    (Fin.last 3, j) e (generic_affine_observability_common_divisor_isUnit 4 hm (by omega))
  apply boundedObservabilityBetaKernel_finrank_zero_of_relation_generator 3
    (genericAffineSquare K n m) (genericAffineRows K n m) _ c
    (fun y hy => ((hgen y).mp hy).exists) j
  · rwa [hc]
  · rw [hc, hdeg]
    omega

theorem generic_corank_one_depth_three_beta_degrees
    (hm : 2 ≤ Fintype.card m) (hn : Fintype.card n + 1 = 4 * Fintype.card m)
    (B : Basis (Fin (Fintype.card n - 3 * Fintype.card m))
      (AffineCoefficientField K (MatrixParameters n m))[X]
      (LinearMap.ker (Matrix.toLin' (observabilityMatrix
        (genericAffineSquare K n m) (genericAffineRows K n m) 3)))) :
    HasMinimalKernelDegrees
      (genericAffineRows K n m * (genericAffineSquare K n m)^3 *
        polynomialKernelBasisMatrix (observabilityMatrix
          (genericAffineSquare K n m) (genericAffineRows K n m) 3) B).transpose
      [10 * Fintype.card m - 4] := by
  have hs : Fintype.card m - (Fintype.card n - 3 * Fintype.card m) = 1 := by omega
  have hw : 6 * Fintype.card m + 4 * (Fintype.card n - 3 * Fintype.card m) =
      10 * Fintype.card m - 4 := by omega
  have hzero := generic_corank_one_depth_three_beta_zero (K := K) hm hn
  have hh := generic_depth_three_beta_degrees_of_single_test (by omega) (by omega)
    B (10 * Fintype.card m - 4) (by omega)
    (by rw [hs, hw, Nat.mul_one])
    (by simpa only [Nat.sub_sub] using hzero)
  rw [hs, hw] at hh
  simpa only [balancedDegreeList, Nat.div_one, Nat.mod_one, Nat.sub_zero,
    List.replicate_zero, List.nil_append, List.replicate_one] using hh

end FD56
