/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericMiddle

/-! Actual generic GL minimal degrees for the family (n,m)=(11k,8k). -/

noncomputable section
namespace FD56
open Matrix Polynomial

theorem generic_family_gl_minimal_degrees {K : Type*} [Field K]
    (k : ℕ) (hk : 0 < k) :
    HasMinimalKernelDegrees (glEquationMatrix
      (genericAffineSquare K (Fin (11 * k)) (Fin (8 * k)))
      (genericAffineRows K (Fin (11 * k)) (Fin (8 * k))))
      (List.replicate (k ^ 2) 5 ++ List.replicate (6 * k ^ 2) 6 ++
        List.replicate (8 * k ^ 2) 7) := by
  have hn : 11 * k - 8 * k = 3 * k := by omega
  have hs : 8 * k - 3 * k = 5 * k := by omega
  have hD : 8 * k + 2 * (3 * k) = 14 * k := by ring
  have hda : 8 * k / (3 * k) = 2 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have hdb : 14 * k / (5 * k) = 2 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have hma : 8 * k % (3 * k) = 2 * k := by rw [Nat.mod_eq_sub_mul_div, hda]; omega
  have hmb : 14 * k % (5 * k) = 4 * k := by rw [Nat.mod_eq_sub_mul_div, hdb]; omega
  have ha : balancedDegreeList (8 * k) (3 * k) =
      List.replicate (2 * k) 3 ++ List.replicate k 2 := by
    simp only [balancedDegreeList, hda, hma]
    rw [show 3 * k - 2 * k = k by omega]
  have hb : balancedDegreeList (14 * k) (5 * k) =
      List.replicate (4 * k) 3 ++ List.replicate k 2 := by
    simp only [balancedDegreeList, hdb, hmb]
    rw [show 5 * k - 4 * k = k by omega]
  have hg := generic_middle_gl_minimal_degrees (K := K)
    (n := Fin (11 * k)) (m := Fin (8 * k)) (by simp; omega) (by simp; omega)
  simp only [Fintype.card_fin, hn, hs, hD, ha, hb] at hg
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [(hasMinimalKernelDegrees_iff_hilbert _ _).mp hg d]
  simp only [degreeConvolution, List.map_flatMap, nat_sum_flatMap,
    List.map_append, List.map_replicate, List.map_map, List.sum_append,
    List.sum_replicate, smul_eq_mul, Function.comp_apply]
  norm_num
  ring

end FD56
