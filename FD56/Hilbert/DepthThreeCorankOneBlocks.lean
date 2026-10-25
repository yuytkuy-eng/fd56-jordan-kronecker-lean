/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthThreeCorankOne
import FD56.Hilbert.ObservabilityBetaBlocks

/-! Repeated corank-one witnesses determine third-depth auxiliary degrees over every field. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K n m t : Type*} [Field K] [Fintype n] [Fintype m] [Fintype t]
  [DecidableEq n] [DecidableEq m] [DecidableEq t]

set_option synthInstance.maxHeartbeats 400000 in
theorem corank_one_repeated_depth_three_beta_zero
    (hm : 2 ≤ Fintype.card m) (hn : Fintype.card n + 1 = 4 * Fintype.card m) :
    Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (boundedObservabilityBetaKernel 3
        (blockDiagonal (fun _ : t => genericAffineSquare K n m))
        (blockDiagonal (fun _ : t => genericAffineRows K n m))
        (10 * Fintype.card m - 5)) = 0 := by
  have hbase : boundedObservabilityBetaKernel 3 (genericAffineSquare K n m)
      (genericAffineRows K n m) (10 * Fintype.card m - 5) = ⊥ :=
    Submodule.finrank_eq_zero.mp (generic_corank_one_depth_three_beta_zero hm hn)
  rw [observability_beta_blocks_eq_bot _ _ 3 _ (fun _ => hbase), finrank_bot]

theorem generic_corank_one_repeated_depth_three_beta_degrees [Nonempty t]
    (hm : 2 ≤ Fintype.card m) (hn : Fintype.card n + 1 = 4 * Fintype.card m)
    (B : Basis (Fin (Fintype.card (n × t) - 3 * Fintype.card (m × t)))
      (AffineCoefficientField K (MatrixParameters (n × t) (m × t)))[X]
      (LinearMap.ker (Matrix.toLin' (observabilityMatrix
        (genericAffineSquare K (n × t) (m × t))
        (genericAffineRows K (n × t) (m × t)) 3)))) :
    HasMinimalKernelDegrees
      (genericAffineRows K (n × t) (m × t) * (genericAffineSquare K (n × t) (m × t))^3 *
        polynomialKernelBasisMatrix (observabilityMatrix
          (genericAffineSquare K (n × t) (m × t))
          (genericAffineRows K (n × t) (m × t)) 3) B).transpose
      (List.replicate (Fintype.card t) (10 * Fintype.card m - 4)) := by
  have ht : 0 < Fintype.card t := Fintype.card_pos
  have hbaseR : Fintype.card n - 3 * Fintype.card m = Fintype.card m - 1 := by omega
  have hbaseW : 6 * Fintype.card m + 4 * (Fintype.card m - 1) =
      10 * Fintype.card m - 4 := by omega
  have hr : Fintype.card (n × t) - 3 * Fintype.card (m × t) =
      (Fintype.card m - 1) * Fintype.card t := by
    simp only [Fintype.card_prod]
    rw [← Nat.mul_assoc, ← Nat.sub_mul, hbaseR]
  have hs : Fintype.card (m × t) -
      (Fintype.card (n × t) - 3 * Fintype.card (m × t)) = Fintype.card t := by
    rw [hr, Fintype.card_prod, ← Nat.sub_mul,
      show Fintype.card m - (Fintype.card m - 1) = 1 by omega, one_mul]
  have hw : 6 * Fintype.card (m × t) +
      4 * (Fintype.card (n × t) - 3 * Fintype.card (m × t)) =
      (10 * Fintype.card m - 4) * Fintype.card t := by
    rw [hr, Fintype.card_prod, ← Nat.mul_assoc, ← Nat.mul_assoc, ← Nat.add_mul, hbaseW]
  have hmn : 3 * Fintype.card (m × t) < Fintype.card (n × t) := by
    simpa only [Fintype.card_prod, Nat.mul_assoc] using
      Nat.mul_lt_mul_of_pos_right (show 3 * Fintype.card m < Fintype.card n by omega) ht
  have hnm : Fintype.card (n × t) < 4 * Fintype.card (m × t) := by
    simpa only [Fintype.card_prod, Nat.mul_assoc] using
      Nat.mul_lt_mul_of_pos_right (show Fintype.card n < 4 * Fintype.card m by omega) ht
  have hM : DegreeBound (blockDiagonal (fun _ : t => genericAffineSquare K n m)) 1 := by
    intro i j
    rw [Matrix.blockDiagonal_apply]
    split_ifs
    · exact genericAffineSquare_degree K n m i.1 j.1
    · simp
  have hP : DegreeBound (blockDiagonal (fun _ : t => genericAffineRows K n m)) 1 := by
    intro i j
    rw [Matrix.blockDiagonal_apply]
    split_ifs
    · exact genericAffineRows_degree K n m i.1 j.1
    · simp
  let σ : K →+* AffineCoefficientField K (MatrixParameters n m) :=
    (algebraMap (MvPolynomial (MatrixParameters n m ⊕ MatrixParameters n m) K)
      (AffineCoefficientField K (MatrixParameters n m))).comp MvPolynomial.C
  have hh := generic_depth_three_beta_degrees_of_single_field_witness σ
    (blockDiagonal (fun _ : t => genericAffineSquare K n m))
    (blockDiagonal (fun _ : t => genericAffineRows K n m)) hM hP hmn hnm B
    (10 * Fintype.card m - 4) (by omega) (by rw [hs, hw])
    (by
      rw [observability_beta_coefficient_kernel_finrank 3 _ _ hM hP]
      simpa only [Nat.sub_sub] using
        corank_one_repeated_depth_three_beta_zero (K := K) (t := t) hm hn)
  rw [hw, hs] at hh
  simpa [balancedDegreeList, Nat.ne_of_gt ht] using hh

end FD56
