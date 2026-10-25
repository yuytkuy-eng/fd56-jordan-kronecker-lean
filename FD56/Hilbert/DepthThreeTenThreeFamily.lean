/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthThreeTenThreeWitness
import FD56.Hilbert.DepthThreeGL
import FD56.Hilbert.ObservabilityBetaBlocks

/-! Repeated ten-state certificates determine the generic third-depth degree lists. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K t : Type*} [Field K] [CharZero K] [Fintype t] [DecidableEq t]

omit [CharZero K] [Fintype t] in
theorem tenThree_repeated_M_degree :
    DegreeBound (blockDiagonal (fun _ : t => tenThreeM (K := K))) 1 := by
  intro i j
  rw [Matrix.blockDiagonal_apply]
  split_ifs
  · exact tenThree_M_degree i.1 j.1
  · simp

omit [CharZero K] [Fintype t] in
theorem tenThree_repeated_P_degree :
    DegreeBound (blockDiagonal (fun _ : t => tenThreeP (K := K))) 1 := by
  intro i j
  rw [Matrix.blockDiagonal_apply]
  split_ifs
  · exact tenThree_P_degree i.1 j.1
  · simp

set_option synthInstance.maxHeartbeats 400000 in
theorem tenThree_repeated_beta_zero :
    Module.finrank K (boundedObservabilityBetaKernel 3
      (blockDiagonal (fun _ : t => tenThreeM (K := K)))
      (blockDiagonal (fun _ : t => tenThreeP (K := K))) 10) = 0 := by
  have hbase : boundedObservabilityBetaKernel 3 (tenThreeM (K := K)) tenThreeP 10 = ⊥ :=
    Submodule.finrank_eq_zero.mp (tenThree_beta_kernel_zero (K := K))
  rw [observability_beta_blocks_eq_bot _ _ 3 10 (fun _ => hbase), finrank_bot]

theorem generic_ten_three_repeated_beta_degrees [Nonempty t]
    (B : Basis (Fin (Fintype.card (Fin 10 × t) - 3 * Fintype.card (Fin 3 × t)))
      (AffineCoefficientField K (MatrixParameters (Fin 10 × t) (Fin 3 × t)))[X]
      (LinearMap.ker (Matrix.toLin' (observabilityMatrix
        (genericAffineSquare K (Fin 10 × t) (Fin 3 × t))
        (genericAffineRows K (Fin 10 × t) (Fin 3 × t)) 3)))) :
    HasMinimalKernelDegrees
      (genericAffineRows K (Fin 10 × t) (Fin 3 × t) *
        (genericAffineSquare K (Fin 10 × t) (Fin 3 × t))^3 *
        polynomialKernelBasisMatrix (observabilityMatrix
          (genericAffineSquare K (Fin 10 × t) (Fin 3 × t))
          (genericAffineRows K (Fin 10 × t) (Fin 3 × t)) 3) B).transpose
      (List.replicate (2 * Fintype.card t) 11) := by
  have ht : 0 < Fintype.card t := Fintype.card_pos
  have hr : Fintype.card (Fin 10 × t) - 3 * Fintype.card (Fin 3 × t) =
      Fintype.card t := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    omega
  have hs : Fintype.card (Fin 3 × t) -
      (Fintype.card (Fin 10 × t) - 3 * Fintype.card (Fin 3 × t)) =
      2 * Fintype.card t := by
    rw [hr]
    simp only [Fintype.card_prod, Fintype.card_fin]
    omega
  have hc : 6 * Fintype.card (Fin 3 × t) +
      4 * (Fintype.card (Fin 10 × t) - 3 * Fintype.card (Fin 3 × t)) =
      11 * (2 * Fintype.card t) := by
    rw [hr]
    simp only [Fintype.card_prod, Fintype.card_fin]
    omega
  have hh := generic_depth_three_beta_degrees_of_single_field_witness
    (RingHom.id K) (blockDiagonal (fun _ : t => tenThreeM (K := K)))
    (blockDiagonal (fun _ : t => tenThreeP (K := K)))
    tenThree_repeated_M_degree tenThree_repeated_P_degree
    (by simp only [Fintype.card_prod, Fintype.card_fin]; omega)
    (by simp only [Fintype.card_prod, Fintype.card_fin]; omega)
    B 11 (by decide) (by rw [hs, hc])
    (by
      rw [observability_beta_coefficient_kernel_finrank 3 _ _
        tenThree_repeated_M_degree tenThree_repeated_P_degree]
      exact tenThree_repeated_beta_zero)
  rw [hc, hs] at hh
  simpa [balancedDegreeList, Nat.ne_of_gt ht] using hh

omit [CharZero K] in
theorem generic_ten_three_repeated_alpha_degrees [Nonempty t] :
    HasMinimalKernelDegrees (observabilityMatrix
      (genericAffineSquare K (Fin 10 × t) (Fin 3 × t))
      (genericAffineRows K (Fin 10 × t) (Fin 3 × t)) 3)
      (List.replicate (Fintype.card t) 18) := by
  have ht : 0 < Fintype.card t := Fintype.card_pos
  have hh := generic_depth_three_alpha_minimal_degrees (K := K)
    (n := Fin 10 × t) (m := Fin 3 × t)
    (by simp only [Fintype.card_prod, Fintype.card_fin]; omega)
  have hr : Fintype.card (Fin 10 × t) - 3 * Fintype.card (Fin 3 × t) =
      Fintype.card t := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    omega
  rw [hr] at hh
  simp only [Fintype.card_prod, Fintype.card_fin] at hh
  rw [show 6 * (3 * Fintype.card t) = 18 * Fintype.card t by ring] at hh
  simpa [balancedDegreeList, Nat.ne_of_gt ht] using hh

theorem generic_ten_three_repeated_gl_minimal_degrees [Nonempty t] :
    HasMinimalKernelDegrees (glEquationMatrix
      (genericAffineSquare K (Fin 10 × t) (Fin 3 × t))
      (genericAffineRows K (Fin 10 × t) (Fin 3 × t)))
      (List.replicate (2 * Fintype.card t ^ 2) 32) := by
  have ht : 0 < Fintype.card t := Fintype.card_pos
  have hrshape : Fintype.card (Fin 10 × t) - 3 * Fintype.card (Fin 3 × t) =
      Fintype.card t := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    omega
  obtain ⟨r, Bv, a, hV, hVL, hperm⟩ :=
    generic_ten_three_repeated_alpha_degrees (K := K) (t := t)
  have hr : r = Fintype.card (Fin 10 × t) - 3 * Fintype.card (Fin 3 × t) := by
    have hh := hperm.length_eq
    rw [List.length_ofFn, List.length_replicate] at hh
    omega
  subst r
  have ha (i) : a i = 18 := by
    have hh := hperm.mem_iff.mp (List.mem_ofFn.mpr ⟨i, rfl⟩)
    exact (List.mem_replicate.mp hh).2
  obtain ⟨s, Bt, b, hT, hTL, hpermT⟩ := generic_ten_three_repeated_beta_degrees Bv
  have hs : s = 2 * Fintype.card t := by simpa using hpermT.length_eq
  have hb (i) : b i = 11 := by
    have hh := hpermT.mem_iff.mp (List.mem_ofFn.mpr ⟨i, rfl⟩)
    exact (List.mem_replicate.mp hh).2
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [generic_depth_three_gl_kernel_hilbert_of_bases
    (by simp only [Fintype.card_prod, Fintype.card_fin]; omega)
    (by simp only [Fintype.card_prod, Fintype.card_fin]; omega)
    Bv Bt a b hV hT hVL hTL d]
  simp only [ha, hb, Nat.reduceAdd, Finset.sum_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, List.map_replicate, List.sum_replicate, smul_eq_mul]
  rw [show 10 * Fintype.card t - 3 * (3 * Fintype.card t) = Fintype.card t by omega, hs]
  ring

end FD56
