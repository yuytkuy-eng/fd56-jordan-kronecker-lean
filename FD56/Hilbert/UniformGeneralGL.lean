/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.UniformGL

/-! Explicit generic GL degrees for every uniform middle family with a ≥ 4. -/

noncomputable section
namespace FD56
open Matrix Polynomial

theorem generic_uniform_gl_minimal_degrees {K : Type*} [Field K]
    (a r : ℕ) (ha : 4 ≤ a) (hr : 0 < r) :
    HasMinimalKernelDegrees (glEquationMatrix
      (genericAffineSquare K (Fin ((a + 1) * r)) (Fin (a * r)))
      (genericAffineRows K (Fin ((a + 1) * r)) (Fin (a * r))))
      (List.replicate ((a - 4) * r ^ 2) (a + 2) ++
        List.replicate (3 * r ^ 2) (a + 3)) := by
  by_cases ha4 : a = 4
  · subst a
    simpa using generic_uniform_four_gl_minimal_degrees (K := K) r hr
  have ha5 : 5 ≤ a := by omega
  have hdiff : (a + 1) * r - a * r = r := by rw [Nat.add_mul, one_mul, Nat.add_sub_cancel_left]
  have hcount : a * r - r = (a - 1) * r := by
    rw [Nat.sub_mul, one_mul]
  have hda : a * r / r = a := by simp [Nat.ne_of_gt hr]
  have hma : a * r % r = 0 := by simp
  have hdb : (a * r + 2 * r) / ((a - 1) * r) = 1 := by
    apply Nat.div_eq_of_lt_le <;> nlinarith [Nat.sub_add_cancel (show 1 ≤ a by omega)]
  have hmb : (a * r + 2 * r) % ((a - 1) * r) = 3 * r := by
    rw [Nat.mod_eq_sub_mul_div, hdb]
    have hh : a * r + 2 * r = (a - 1) * r * 1 + 3 * r := by
      nlinarith [Nat.sub_add_cancel (show 1 ≤ a by omega)]
    rw [hh, Nat.add_sub_cancel_left]
  have hleft : (a - 1) * r - 3 * r = (a - 4) * r := by
    have hh : (a - 1) * r = 3 * r + (a - 4) * r := by
      nlinarith [Nat.sub_add_cancel (show 1 ≤ a by omega), Nat.sub_add_cancel ha]
    rw [hh, Nat.add_sub_cancel_left]
  have halpha : balancedDegreeList (a * r) r = List.replicate r a := by
    simp [balancedDegreeList, hda, hma]
  have hbeta : balancedDegreeList (a * r + 2 * r) ((a - 1) * r) =
      List.replicate (3 * r) 2 ++ List.replicate ((a - 4) * r) 1 := by
    simp [balancedDegreeList, hdb, hmb, hleft]
  have hg := generic_middle_gl_minimal_degrees (K := K)
    (n := Fin ((a + 1) * r)) (m := Fin (a * r))
    (by simp; nlinarith) (by simp; nlinarith)
  simp only [Fintype.card_fin, hdiff, hcount, halpha, hbeta] at hg
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [(hasMinimalKernelDegrees_iff_hilbert _ _).mp hg d]
  simp only [degreeConvolution, List.map_flatMap, nat_sum_flatMap,
    List.map_append, List.map_replicate, List.map_map, List.sum_append,
    List.sum_replicate, smul_eq_mul, Function.comp_apply]
  ring

end FD56
