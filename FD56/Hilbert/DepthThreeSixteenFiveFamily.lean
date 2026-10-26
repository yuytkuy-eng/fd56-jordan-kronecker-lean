/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthThreeSixteenFiveWitness
import FD56.Hilbert.DepthThreeGL
import FD56.Hilbert.DepthThreeBetaCriterion
import FD56.Hilbert.ObservabilityBetaBlockDimension
import FD56.Hilbert.ConvolutionDegrees

/-! Repeated sixteen-state certificates give two adjacent generic third-depth degrees. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K t : Type*} [Field K] [CharZero K] [Fintype t] [DecidableEq t]

theorem generic_sixteen_five_repeated_beta_degrees [Nonempty t]
    (B : Basis (Fin (Fintype.card (Fin 16 × t) - 3 * Fintype.card (Fin 5 × t)))
      (AffineCoefficientField K (MatrixParameters (Fin 16 × t) (Fin 5 × t)))[X]
      (LinearMap.ker (Matrix.toLin' (observabilityMatrix
        (genericAffineSquare K (Fin 16 × t) (Fin 5 × t))
        (genericAffineRows K (Fin 16 × t) (Fin 5 × t)) 3)))) :
    HasMinimalKernelDegrees
      (genericAffineRows K (Fin 16 × t) (Fin 5 × t) *
        (genericAffineSquare K (Fin 16 × t) (Fin 5 × t))^3 *
        polynomialKernelBasisMatrix (observabilityMatrix
          (genericAffineSquare K (Fin 16 × t) (Fin 5 × t))
          (genericAffineRows K (Fin 16 × t) (Fin 5 × t)) 3) B).transpose
      (List.replicate (2 * Fintype.card t) 8 ++ List.replicate (2 * Fintype.card t) 9) := by
  let M := sixteenFiveM (K := K)
  let P := sixteenFiveP (K := K)
  have hM : DegreeBound M 1 := sixteenFive_M_degree
  have hP : DegreeBound P 1 := sixteenFive_P_degree
  have hzero : Module.finrank K (boundedObservabilityBetaKernel 3 M P 7) = 0 :=
    sixteenFive_beta_kernel_zero
  have hcritical : Module.finrank K (boundedObservabilityBetaKernel 3 M P 8) ≤ 2 :=
    sixteenFive_beta_kernel_eight_le
  have ht : 0 < Fintype.card t := Fintype.card_pos
  have hMD : DegreeBound (blockDiagonal (fun _ : t => M)) 1 := by
    intro i j
    rw [Matrix.blockDiagonal_apply]
    split_ifs
    · exact hM i.1 j.1
    · simp
  have hPD : DegreeBound (blockDiagonal (fun _ : t => P)) 1 := by
    intro i j
    rw [Matrix.blockDiagonal_apply]
    split_ifs
    · exact hP i.1 j.1
    · simp
  have hz : Module.finrank K (boundedObservabilityBetaKernel 3
      (blockDiagonal (fun _ : t => M)) (blockDiagonal (fun _ : t => P)) 7) = 0 := by
    rw [observability_beta_blocks_finrank]
    simp only [hzero, Finset.sum_const_zero]
  have hc : Module.finrank K (boundedObservabilityBetaKernel 3
      (blockDiagonal (fun _ : t => M)) (blockDiagonal (fun _ : t => P)) 8) ≤
      2 * Fintype.card t := by
    rw [observability_beta_blocks_finrank]
    calc
      _ ≤ ∑ _ : t, 2 := Finset.sum_le_sum (fun _ _ => hcritical)
      _ = 2 * Fintype.card t := by simp [Nat.mul_comm]
  have hs : 2 * Fintype.card t + 2 * Fintype.card t = Fintype.card (Fin 5 × t) -
      (Fintype.card (Fin 16 × t) - 3 * Fintype.card (Fin 5 × t)) := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    omega
  have hw : 8 * (2 * Fintype.card t + 2 * Fintype.card t) + 2 * Fintype.card t =
      6 * Fintype.card (Fin 5 × t) +
        4 * (Fintype.card (Fin 16 × t) - 3 * Fintype.card (Fin 5 × t)) := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    omega
  have hh := generic_depth_three_beta_degrees_of_two_field_witnesses
    (RingHom.id K) (blockDiagonal (fun _ : t => M)) (blockDiagonal (fun _ : t => M))
    (blockDiagonal (fun _ : t => P)) (blockDiagonal (fun _ : t => P))
    hMD hMD hPD hPD
    (by simp only [Fintype.card_prod, Fintype.card_fin]; omega)
    (by simp only [Fintype.card_prod, Fintype.card_fin]; omega)
    B 8 (2 * Fintype.card t) (2 * Fintype.card t) (by decide) hs hw
    (by rw [observability_beta_coefficient_kernel_finrank 3 _ _ hMD hPD]; exact hz)
    (by rw [observability_beta_coefficient_kernel_finrank 3 _ _ hMD hPD]; exact hc)
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [(hasMinimalKernelDegrees_iff_hilbert _ _).mp hh d, ← hs, ← hw,
    balancedDegreeList_hilbert _ _ d (by omega)]
  simpa only [List.map_append, List.map_replicate, List.sum_append,
    List.sum_replicate, smul_eq_mul, Nat.reduceAdd] using
      (adjacent_degree_hilbert (2 * Fintype.card t) (2 * Fintype.card t) 8 d).symm

omit [CharZero K] in
theorem generic_sixteen_five_repeated_alpha_degrees [Nonempty t] :
    HasMinimalKernelDegrees (observabilityMatrix
      (genericAffineSquare K (Fin 16 × t) (Fin 5 × t))
      (genericAffineRows K (Fin 16 × t) (Fin 5 × t)) 3)
      (List.replicate (Fintype.card t) 30) := by
  have ht : 0 < Fintype.card t := Fintype.card_pos
  have hh := generic_depth_three_alpha_minimal_degrees (K := K)
    (n := Fin 16 × t) (m := Fin 5 × t)
    (by simp only [Fintype.card_prod, Fintype.card_fin]; omega)
  have hr : Fintype.card (Fin 16 × t) - 3 * Fintype.card (Fin 5 × t) =
      Fintype.card t := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    omega
  rw [hr] at hh
  simp only [Fintype.card_prod, Fintype.card_fin] at hh
  rw [show 6 * (5 * Fintype.card t) = 30 * Fintype.card t by ring] at hh
  simpa [balancedDegreeList, Nat.ne_of_gt ht] using hh

theorem generic_sixteen_five_repeated_gl_minimal_degrees [Nonempty t] :
    HasMinimalKernelDegrees (glEquationMatrix
      (genericAffineSquare K (Fin 16 × t) (Fin 5 × t))
      (genericAffineRows K (Fin 16 × t) (Fin 5 × t)))
      (List.replicate (2 * Fintype.card t ^ 2) 41 ++
        List.replicate (2 * Fintype.card t ^ 2) 42) := by
  have ht : 0 < Fintype.card t := Fintype.card_pos
  have hrshape : Fintype.card (Fin 16 × t) - 3 * Fintype.card (Fin 5 × t) =
      Fintype.card t := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    omega
  obtain ⟨r, Bv, a, hV, hVL, hperm⟩ := generic_sixteen_five_repeated_alpha_degrees (K := K) (t := t)
  have hr : r = Fintype.card (Fin 16 × t) - 3 * Fintype.card (Fin 5 × t) := by
    have hh := hperm.length_eq
    rw [List.length_ofFn, List.length_replicate] at hh
    omega
  subst r
  obtain ⟨s, Bt, b, hT, hTL, hpermT⟩ := generic_sixteen_five_repeated_beta_degrees Bv
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [generic_depth_three_gl_kernel_hilbert_of_bases
    (by simp only [Fintype.card_prod, Fintype.card_fin]; omega)
    (by simp only [Fintype.card_prod, Fintype.card_fin]; omega)
    Bv Bt a b hV hT hVL hTL d]
  rw [sum_pairs_of_permuted_degrees a b _ _ hperm hpermT
    (fun x y => d + 1 - (x + y + 3)), nat_sum_flatMap]
  simp only [List.map_replicate, List.sum_replicate, List.map_append, List.sum_append,
    smul_eq_mul, Nat.reduceAdd]
  ring

end FD56
