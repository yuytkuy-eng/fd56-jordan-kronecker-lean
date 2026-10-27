/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthThreeEighteenFiveWitness
import FD56.Hilbert.DepthThreeGL
import FD56.Hilbert.DepthThreeBetaSingleTest
import FD56.Hilbert.ObservabilityBetaBlockDimension
import FD56.Hilbert.ConvolutionDegrees

/-! Repeated eighteen-state certificates give equal generic third-depth degrees. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K t : Type*} [Field K] [CharZero K] [Fintype t] [DecidableEq t]

theorem generic_eighteen_five_repeated_beta_degrees [Nonempty t]
    (B : Basis (Fin (Fintype.card (Fin 18 × t) - 3 * Fintype.card (Fin 5 × t)))
      (AffineCoefficientField K (MatrixParameters (Fin 18 × t) (Fin 5 × t)))[X]
      (LinearMap.ker (Matrix.toLin' (observabilityMatrix
        (genericAffineSquare K (Fin 18 × t) (Fin 5 × t))
        (genericAffineRows K (Fin 18 × t) (Fin 5 × t)) 3)))) :
    HasMinimalKernelDegrees
      (genericAffineRows K (Fin 18 × t) (Fin 5 × t) *
        (genericAffineSquare K (Fin 18 × t) (Fin 5 × t))^3 *
        polynomialKernelBasisMatrix (observabilityMatrix
          (genericAffineSquare K (Fin 18 × t) (Fin 5 × t))
          (genericAffineRows K (Fin 18 × t) (Fin 5 × t)) 3) B).transpose
      (List.replicate (2 * Fintype.card t) 21) := by
  let M := eighteenFiveM (K := K)
  let P := eighteenFiveP (K := K)
  have ht : 0 < Fintype.card t := Fintype.card_pos
  have hMD : DegreeBound (blockDiagonal (fun _ : t => M)) 1 := by
    intro i j
    rw [Matrix.blockDiagonal_apply]
    split_ifs
    · exact eighteenFive_M_degree i.1 j.1
    · simp
  have hPD : DegreeBound (blockDiagonal (fun _ : t => P)) 1 := by
    intro i j
    rw [Matrix.blockDiagonal_apply]
    split_ifs
    · exact eighteenFive_P_degree i.1 j.1
    · simp
  have hz : Module.finrank K (boundedObservabilityBetaKernel 3
      (blockDiagonal (fun _ : t => M)) (blockDiagonal (fun _ : t => P)) 20) = 0 := by
    rw [observability_beta_blocks_finrank]
    have hh : Module.finrank K (boundedObservabilityBetaKernel 3 M P 20) = 0 :=
      eighteenFive_beta_kernel_zero
    simp only [hh,Finset.sum_const_zero]
  have hs : Fintype.card (Fin 5 × t) -
      (Fintype.card (Fin 18 × t) - 3 * Fintype.card (Fin 5 × t)) = 2 * Fintype.card t := by
    simp only [Fintype.card_prod,Fintype.card_fin]
    omega
  have hw : 6 * Fintype.card (Fin 5 × t) +
      4 * (Fintype.card (Fin 18 × t) - 3 * Fintype.card (Fin 5 × t)) =
      21 * (2 * Fintype.card t) := by
    simp only [Fintype.card_prod,Fintype.card_fin]
    omega
  have hh := generic_depth_three_beta_degrees_of_single_field_witness
    (RingHom.id K) (blockDiagonal (fun _ : t => M)) (blockDiagonal (fun _ : t => P))
    hMD hPD
    (by simp only [Fintype.card_prod,Fintype.card_fin]; omega)
    (by simp only [Fintype.card_prod,Fintype.card_fin]; omega)
    B 21 (by decide) (by rw [hs,hw])
    (by rw [observability_beta_coefficient_kernel_finrank 3 _ _ hMD hPD]; exact hz)
  rw [hs,hw] at hh
  simpa [balancedDegreeList,Nat.ne_of_gt (by omega : 0 < 2 * Fintype.card t)] using hh

omit [CharZero K] in
theorem generic_eighteen_five_repeated_alpha_degrees [Nonempty t] :
    HasMinimalKernelDegrees (observabilityMatrix
      (genericAffineSquare K (Fin 18 × t) (Fin 5 × t))
      (genericAffineRows K (Fin 18 × t) (Fin 5 × t)) 3)
      (List.replicate (3 * Fintype.card t) 10) := by
  have ht : 0 < Fintype.card t := Fintype.card_pos
  have hh := generic_depth_three_alpha_minimal_degrees (K := K)
    (n := Fin 18 × t) (m := Fin 5 × t)
    (by simp only [Fintype.card_prod, Fintype.card_fin]; omega)
  have hr : Fintype.card (Fin 18 × t) - 3 * Fintype.card (Fin 5 × t) =
      3 * Fintype.card t := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    omega
  rw [hr] at hh
  simp only [Fintype.card_prod, Fintype.card_fin] at hh
  rw [show 6 * (5 * Fintype.card t) = 10 * (3 * Fintype.card t) by ring] at hh
  simpa [balancedDegreeList, Nat.ne_of_gt ht, Nat.ne_of_gt (by omega : 0 < 3 * Fintype.card t)] using hh

theorem generic_eighteen_five_repeated_gl_minimal_degrees [Nonempty t] :
    HasMinimalKernelDegrees (glEquationMatrix
      (genericAffineSquare K (Fin 18 × t) (Fin 5 × t))
      (genericAffineRows K (Fin 18 × t) (Fin 5 × t)))
      (List.replicate (6 * Fintype.card t ^ 2) 34) := by
  have ht : 0 < Fintype.card t := Fintype.card_pos
  have hrshape : Fintype.card (Fin 18 × t) - 3 * Fintype.card (Fin 5 × t) =
      3 * Fintype.card t := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    omega
  obtain ⟨r, Bv, a, hV, hVL, hperm⟩ := generic_eighteen_five_repeated_alpha_degrees (K := K) (t := t)
  have hr : r = Fintype.card (Fin 18 × t) - 3 * Fintype.card (Fin 5 × t) := by
    have hh := hperm.length_eq
    rw [List.length_ofFn, List.length_replicate] at hh
    omega
  subst r
  obtain ⟨s, Bt, b, hT, hTL, hpermT⟩ := generic_eighteen_five_repeated_beta_degrees Bv
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
