/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericMiddle

/-! Explicit GL degree lists for auxiliary degrees three and four. -/

noncomputable section
namespace FD56
open Matrix Polynomial

theorem generic_mixed_three_gl_minimal_degrees {K : Type*} [Field K]
    (u v : ℕ) (hu : 0 < u) (hv : 0 < v) :
    HasMinimalKernelDegrees (glEquationMatrix
      (genericAffineSquare K (Fin (4 * (u + v) + v)) (Fin (3 * (u + v) + v)))
      (genericAffineRows K (Fin (4 * (u + v) + v)) (Fin (3 * (u + v) + v))))
      (List.replicate (u * (u + 3 * v)) 6 ++
        List.replicate (u ^ 2 + u * v + 3 * v ^ 2) 7 ++
        List.replicate (u * v) 8) := by
  let r := u + v
  have hr : 0 < r := by dsimp [r]; omega
  have hvlt : v < r := by dsimp [r]; omega
  have hdiff : 4 * r + v - (3 * r + v) = r := by omega
  have hcount : 3 * r + v - r = 2 * r + v := by omega
  have hda : (3 * r + v) / r = 3 := by
    apply Nat.div_eq_of_lt_le <;> omega
  have hma : (3 * r + v) % r = v := by
    rw [Nat.mod_eq_sub_mul_div, hda]
    omega
  have hdb : (3 * r + v + 2 * r) / (2 * r + v) = 2 := by
    apply Nat.div_eq_of_lt_le <;> omega
  have hmb : (3 * r + v + 2 * r) % (2 * r + v) = u := by
    rw [Nat.mod_eq_sub_mul_div, hdb]
    dsimp [r]
    omega
  have halpha : balancedDegreeList (3 * r + v) r =
      List.replicate v 4 ++ List.replicate u 3 := by
    have hh : r - v = u := by dsimp [r]; omega
    simp [balancedDegreeList, hda, hma, hh]
  have hbeta : balancedDegreeList (3 * r + v + 2 * r) (2 * r + v) =
      List.replicate u 3 ++ List.replicate (u + 3 * v) 2 := by
    have hh : 2 * r + v - u = u + 3 * v := by dsimp [r]; omega
    simp [balancedDegreeList, hdb, hmb, hh]
  have hg := generic_middle_gl_minimal_degrees (K := K)
    (n := Fin (4 * r + v)) (m := Fin (3 * r + v))
    (by simp; omega) (by simp; omega)
  simp only [Fintype.card_fin, hdiff, hcount, halpha, hbeta] at hg
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [(hasMinimalKernelDegrees_iff_hilbert _ _).mp hg d]
  simp only [degreeConvolution, List.map_flatMap, nat_sum_flatMap,
    List.map_append, List.map_replicate, List.map_map, List.sum_append,
    List.sum_replicate, smul_eq_mul, Function.comp_apply]
  norm_num
  ring

end FD56
