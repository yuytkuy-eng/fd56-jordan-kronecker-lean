/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericMiddle

/-! The generic GL degree list for (n,m)=(5r,4r) is constant. -/

noncomputable section
namespace FD56
open Matrix Polynomial

theorem generic_uniform_four_gl_minimal_degrees {K : Type*} [Field K]
    (r : ℕ) (hr : 0 < r) :
    HasMinimalKernelDegrees (glEquationMatrix
      (genericAffineSquare K (Fin (5 * r)) (Fin (4 * r)))
      (genericAffineRows K (Fin (5 * r)) (Fin (4 * r))))
      (List.replicate (3 * r ^ 2) 7) := by
  have hn : 5 * r - 4 * r = r := by omega
  have hs : 4 * r - r = 3 * r := by omega
  have hD : 4 * r + 2 * r = 6 * r := by omega
  have hda : 4 * r / r = 4 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have hdb : 6 * r / (3 * r) = 2 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have hma : 4 * r % r = 0 := by rw [Nat.mod_eq_sub_mul_div, hda]; omega
  have hmb : 6 * r % (3 * r) = 0 := by rw [Nat.mod_eq_sub_mul_div, hdb]; omega
  have ha : balancedDegreeList (4 * r) r = List.replicate r 4 := by
    simp [balancedDegreeList, hda, hma]
  have hb : balancedDegreeList (6 * r) (3 * r) = List.replicate (3 * r) 2 := by
    simp [balancedDegreeList, hdb, hmb]
  have hg := generic_middle_gl_minimal_degrees (K := K)
    (n := Fin (5 * r)) (m := Fin (4 * r)) (by simp; omega) (by simp; omega)
  simp only [Fintype.card_fin, hn, hs, hD, ha, hb] at hg
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [(hasMinimalKernelDegrees_iff_hilbert _ _).mp hg d]
  simp only [degreeConvolution, List.map_flatMap, nat_sum_flatMap,
    List.map_replicate, List.map_map, List.sum_replicate, smul_eq_mul, Function.comp_apply]
  norm_num
  ring

end FD56
