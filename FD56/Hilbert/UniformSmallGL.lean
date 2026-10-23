/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.UniformGL

/-! Explicit GL degree lists for the two smallest nondivisible uniform families. -/

noncomputable section
namespace FD56
open Matrix Polynomial

theorem generic_uniform_two_gl_minimal_degrees {K : Type*} [Field K]
    (r : ℕ) (hr : 0 < r) :
    HasMinimalKernelDegrees (glEquationMatrix
      (genericAffineSquare K (Fin (3 * r)) (Fin (2 * r)))
      (genericAffineRows K (Fin (3 * r)) (Fin (2 * r))))
      (List.replicate (r ^ 2) 7) := by
  have hn : 3 * r - 2 * r = r := by omega
  have hs : 2 * r - r = 1 * r := by omega
  have hD : 2 * r + 2 * r = 4 * r := by omega
  have hda : 2 * r / r = 2 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have hdb : 4 * r / (1 * r) = 4 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have hma : 2 * r % r = 0 := by rw [Nat.mod_eq_sub_mul_div, hda]; omega
  have hmb : 4 * r % (1 * r) = 0 * r := by
    rw [Nat.mod_eq_sub_mul_div, hdb]; omega
  have halpha : balancedDegreeList (2 * r) r = List.replicate r 2 := by
    simp [balancedDegreeList, hda, hma]
  have hbeta : balancedDegreeList (4 * r) (1 * r) = List.replicate r 4 := by
    simp only [balancedDegreeList, hdb, hmb]
    simp
  have hg := generic_middle_gl_minimal_degrees (K := K)
    (n := Fin (3 * r)) (m := Fin (2 * r)) (by simp; omega) (by simp; omega)
  simp only [Fintype.card_fin, hn, hs, hD, halpha, hbeta] at hg
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [(hasMinimalKernelDegrees_iff_hilbert _ _).mp hg d]
  simp only [degreeConvolution, List.map_flatMap, nat_sum_flatMap,
    List.map_append, List.map_replicate, List.map_map, List.sum_append,
    List.sum_replicate, smul_eq_mul, Function.comp_apply]
  norm_num
  ring

theorem generic_uniform_three_gl_minimal_degrees {K : Type*} [Field K]
    (r : ℕ) (hr : 0 < r) :
    HasMinimalKernelDegrees (glEquationMatrix
      (genericAffineSquare K (Fin (4 * r)) (Fin (3 * r)))
      (genericAffineRows K (Fin (4 * r)) (Fin (3 * r))))
      (List.replicate (r ^ 2) 6 ++ List.replicate (r ^ 2) 7) := by
  have hn : 4 * r - 3 * r = r := by omega
  have hs : 3 * r - r = 2 * r := by omega
  have hD : 3 * r + 2 * r = 5 * r := by omega
  have hda : 3 * r / r = 3 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have hdb : 5 * r / (2 * r) = 2 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have hma : 3 * r % r = 0 := by rw [Nat.mod_eq_sub_mul_div, hda]; omega
  have hmb : 5 * r % (2 * r) = 1 * r := by
    rw [Nat.mod_eq_sub_mul_div, hdb]; omega
  have halpha : balancedDegreeList (3 * r) r = List.replicate r 3 := by
    simp [balancedDegreeList, hda, hma]
  have hbeta : balancedDegreeList (5 * r) (2 * r) =
      List.replicate r 3 ++ List.replicate r 2 := by
    have hh : 2 * r - r = r := by omega
    simp [balancedDegreeList, hdb, hmb, hh]
  have hg := generic_middle_gl_minimal_degrees (K := K)
    (n := Fin (4 * r)) (m := Fin (3 * r)) (by simp; omega) (by simp; omega)
  simp only [Fintype.card_fin, hn, hs, hD, halpha, hbeta] at hg
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [(hasMinimalKernelDegrees_iff_hilbert _ _).mp hg d]
  simp only [degreeConvolution, List.map_flatMap, nat_sum_flatMap,
    List.map_append, List.map_replicate, List.map_map, List.sum_append,
    List.sum_replicate, smul_eq_mul, Function.comp_apply]
  norm_num
  ring

end FD56
