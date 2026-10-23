/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericMiddle

/-! Explicit GL degree lists when the first auxiliary degrees are a and a+1. -/

noncomputable section
namespace FD56
open Matrix Polynomial

theorem generic_mixed_gl_minimal_degrees {K : Type*} [Field K]
    (a u v : ℕ) (ha : 4 ≤ a) (hu : 0 < u) (hv : 0 < v) :
    let r := u + v
    let g := (a - 4) * r + v
    HasMinimalKernelDegrees (glEquationMatrix
      (genericAffineSquare K (Fin ((a + 1) * r + v)) (Fin (a * r + v)))
      (genericAffineRows K (Fin ((a + 1) * r + v)) (Fin (a * r + v))))
      (List.replicate (u * g) (a + 2) ++
        List.replicate (3 * u * r + v * g) (a + 3) ++
        List.replicate (3 * v * r) (a + 4)) := by
  dsimp
  let r := u + v
  have hr : 0 < r := by dsimp [r]; omega
  have hvlt : v < r := by dsimp [r]; omega
  have hdiff : (a + 1) * r + v - (a * r + v) = r := by
    have hh : (a + 1) * r + v = (a * r + v) + r := by ring
    rw [hh, Nat.add_sub_cancel_left]
  have hcount : a * r + v - r = (a - 1) * r + v := by
    have hh : a * r + v = r + ((a - 1) * r + v) := by
      nlinarith only [congrArg (fun z => z * r) (Nat.sub_add_cancel (show 1 ≤ a by omega))]
    rw [hh, Nat.add_sub_cancel_left]
  have hda : (a * r + v) / r = a := by
    apply Nat.div_eq_of_lt_le <;> nlinarith
  have hma : (a * r + v) % r = v := by
    rw [Nat.mod_eq_sub_mul_div, hda, Nat.mul_comm r a, Nat.add_sub_cancel_left]
  have hdb : (a * r + v + 2 * r) / ((a - 1) * r + v) = 1 := by
    apply Nat.div_eq_of_lt_le <;>
      nlinarith only [hr, hv, ha,
        congrArg (fun z => z * r) (Nat.sub_add_cancel (show 1 ≤ a by omega)),
        Nat.mul_le_mul_right r ha]
  have hmb : (a * r + v + 2 * r) % ((a - 1) * r + v) = 3 * r := by
    rw [Nat.mod_eq_sub_mul_div, hdb]
    have hh : a * r + v + 2 * r = ((a - 1) * r + v) * 1 + 3 * r := by
      nlinarith only [congrArg (fun z => z * r) (Nat.sub_add_cancel (show 1 ≤ a by omega))]
    rw [hh, Nat.add_sub_cancel_left]
  have hleft : (a - 1) * r + v - 3 * r = (a - 4) * r + v := by
    have hh : (a - 1) * r + v = 3 * r + ((a - 4) * r + v) := by
      nlinarith only [congrArg (fun z => z * r) (Nat.sub_add_cancel (show 1 ≤ a by omega)),
        congrArg (fun z => z * r) (Nat.sub_add_cancel ha)]
    rw [hh, Nat.add_sub_cancel_left]
  have halpha : balancedDegreeList (a * r + v) r =
      List.replicate v (a + 1) ++ List.replicate u a := by
    have hh : r - v = u := by dsimp [r]; omega
    simp [balancedDegreeList, hda, hma, hh]
  have hbeta : balancedDegreeList (a * r + v + 2 * r) ((a - 1) * r + v) =
      List.replicate (3 * r) 2 ++ List.replicate ((a - 4) * r + v) 1 := by
    simp [balancedDegreeList, hdb, hmb, hleft]
  have hg := generic_middle_gl_minimal_degrees (K := K)
    (n := Fin ((a + 1) * r + v)) (m := Fin (a * r + v))
    (by simp; nlinarith) (by simp; nlinarith)
  simp only [Fintype.card_fin, hdiff, hcount, halpha, hbeta] at hg
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [(hasMinimalKernelDegrees_iff_hilbert _ _).mp hg d]
  simp only [degreeConvolution, List.map_flatMap, nat_sum_flatMap,
    List.map_append, List.map_replicate, List.map_map, List.sum_append,
    List.sum_replicate, smul_eq_mul, Function.comp_apply]
  simp only [Nat.add_assoc]
  dsimp [r]
  ring

end FD56
