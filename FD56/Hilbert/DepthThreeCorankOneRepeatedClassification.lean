/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthThreeCorankOneBlocks
import FD56.Hilbert.DepthThreeGL
import FD56.Hilbert.ConvolutionDegrees

/-! Generic GL minimal degrees for repetitions of a third-depth corank-one size pair. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K n m t : Type*} [Field K]
  [Fintype n] [Fintype m] [Fintype t]
  [DecidableEq n] [DecidableEq m] [DecidableEq t] [Nonempty t]

theorem generic_corank_one_repeated_depth_three_gl_minimal_degrees
    (hm : 2 ≤ Fintype.card m) (hn : Fintype.card n + 1 = 4 * Fintype.card m) :
    HasMinimalKernelDegrees (glEquationMatrix
      (genericAffineSquare K (n × t) (m × t)) (genericAffineRows K (n × t) (m × t)))
      ((balancedDegreeList (6 * Fintype.card (m × t))
        (Fintype.card (n × t) - 3 * Fintype.card (m × t))).flatMap
          (fun a => List.replicate (Fintype.card t) (a + (10 * Fintype.card m - 1)))) := by
  have ht : 0 < Fintype.card t := Fintype.card_pos
  have hmn : 3 * Fintype.card (m × t) < Fintype.card (n × t) := by
    simp only [Fintype.card_prod]
    nlinarith
  have hnm : Fintype.card (n × t) ≤ 4 * Fintype.card (m × t) := by
    simp only [Fintype.card_prod]
    nlinarith
  obtain ⟨r, Bv, a, hV, hVL, hperm⟩ :=
    generic_depth_three_alpha_minimal_degrees (K := K) hmn
  have hr : r = Fintype.card (n × t) - 3 * Fintype.card (m × t) := by
    simpa only [List.length_ofFn, balancedDegreeList_length (6 * Fintype.card (m × t))
      (Fintype.card (n × t) - 3 * Fintype.card (m × t)) (by omega)] using hperm.length_eq
  subst r
  obtain ⟨s, Bt, b, hT, hTL, hpermT⟩ :=
    generic_corank_one_repeated_depth_three_beta_degrees hm hn Bv
  have hshift : 10 * Fintype.card m - 4 + 3 = 10 * Fintype.card m - 1 := by omega
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [generic_depth_three_gl_kernel_hilbert_of_bases hmn hnm
    Bv Bt a b hV hT hVL hTL d]
  have hh := sum_pairs_of_permuted_degrees a b _ _ hperm hpermT
    (fun x y => d + 1 - (x + y + 3))
  simpa only [List.map_flatMap, List.map_replicate, Nat.add_assoc, hshift] using hh

theorem generic_seven_two_repeated_gl_minimal_degrees_all_fields :
    HasMinimalKernelDegrees (glEquationMatrix
      (genericAffineSquare K (Fin 7 × t) (Fin 2 × t))
      (genericAffineRows K (Fin 7 × t) (Fin 2 × t)))
      (List.replicate (Fintype.card t ^ 2) 31) := by
  have ht : 0 < Fintype.card t := Fintype.card_pos
  have halpha : balancedDegreeList (6 * Fintype.card (Fin 2 × t))
      (Fintype.card (Fin 7 × t) - 3 * Fintype.card (Fin 2 × t)) =
      List.replicate (Fintype.card t) 12 := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    rw [show 7 * Fintype.card t - 3 * (2 * Fintype.card t) = Fintype.card t by omega,
      show 6 * (2 * Fintype.card t) = 12 * Fintype.card t by ring]
    simp [balancedDegreeList, Nat.ne_of_gt ht]
  have hh := generic_corank_one_repeated_depth_three_gl_minimal_degrees
    (K := K) (n := Fin 7) (m := Fin 2) (t := t) (by norm_num) (by norm_num)
  rw [halpha] at hh
  simpa [List.flatMap_replicate, List.flatten_replicate_replicate, pow_two] using hh

theorem generic_eleven_three_repeated_gl_minimal_degrees_all_fields :
    HasMinimalKernelDegrees (glEquationMatrix
      (genericAffineSquare K (Fin 11 × t) (Fin 3 × t))
      (genericAffineRows K (Fin 11 × t) (Fin 3 × t)))
      (List.replicate (2 * Fintype.card t ^ 2) 38) := by
  have ht : 0 < Fintype.card t := Fintype.card_pos
  have halpha : balancedDegreeList (6 * Fintype.card (Fin 3 × t))
      (Fintype.card (Fin 11 × t) - 3 * Fintype.card (Fin 3 × t)) =
      List.replicate (2 * Fintype.card t) 9 := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    rw [show 11 * Fintype.card t - 3 * (3 * Fintype.card t) = 2 * Fintype.card t by omega,
      show 6 * (3 * Fintype.card t) = 9 * (2 * Fintype.card t) by ring]
    simp [balancedDegreeList, Nat.ne_of_gt ht]
  have hh := generic_corank_one_repeated_depth_three_gl_minimal_degrees
    (K := K) (n := Fin 11) (m := Fin 3) (t := t) (by norm_num) (by norm_num)
  rw [halpha] at hh
  simpa [List.flatMap_replicate, List.flatten_replicate_replicate, pow_two, Nat.mul_assoc]
    using hh

end FD56
