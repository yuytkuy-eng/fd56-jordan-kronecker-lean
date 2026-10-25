/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GLKirillovPencil
import FD56.Hilbert.DepthThreeCorankOneRepeatedClassification

/-! Minimal degrees and the dimension budget for the actual corank-one Kirillov pencil.
These statements do not construct a constant congruence to canonical blocks. -/

namespace FD56
open Matrix Polynomial

theorem shifted_repeated_block_dimension (xs : List ℕ) (d k : ℕ) :
    ((xs.flatMap (fun a => List.replicate k (a + d))).map (fun e => 2 * e + 1)).sum =
      k * (2 * xs.sum + (2 * d + 1) * xs.length) := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.flatMap_cons, List.map_append, List.map_replicate, List.sum_append,
      List.sum_replicate, smul_eq_mul, List.sum_cons, List.length_cons, ih]
    ring

variable {K n m t : Type*} [Field K] [Fintype n] [Fintype m] [Fintype t]
  [DecidableEq n] [DecidableEq m] [DecidableEq t] [Nonempty t]

theorem generic_corank_one_repeated_kirillov_minimal_degrees
    (hm : 2 ≤ Fintype.card m) (hn : Fintype.card n + 1 = 4 * Fintype.card m) :
    HasMinimalKernelDegrees (glKirillovMatrix
      (genericAffineSquare K (n × t) (m × t)) (genericAffineRows K (n × t) (m × t)))
      ((balancedDegreeList (6 * Fintype.card (m × t))
        (Fintype.card (n × t) - 3 * Fintype.card (m × t))).flatMap
          (fun a => List.replicate (Fintype.card t) (a + (10 * Fintype.card m - 1)))) := by
  apply (glKirillovMatrix_hasMinimalKernelDegrees_iff _ _ _).mpr
  exact generic_corank_one_repeated_depth_three_gl_minimal_degrees hm hn

omit [Field K] [DecidableEq n] [DecidableEq m] [DecidableEq t] in
theorem corank_one_repeated_kirillov_dimension_budget
    (hm : 2 ≤ Fintype.card m) (hn : Fintype.card n + 1 = 4 * Fintype.card m) :
    (((balancedDegreeList (6 * Fintype.card (m × t))
        (Fintype.card (n × t) - 3 * Fintype.card (m × t))).flatMap
          (fun a => List.replicate (Fintype.card t) (a + (10 * Fintype.card m - 1)))).map
      (fun e => 2 * e + 1)).sum = Fintype.card (SLInput (n × t) (m × t)) := by
  have ht : 0 < Fintype.card t := Fintype.card_pos
  have hpos : 0 < Fintype.card (n × t) - 3 * Fintype.card (m × t) := by
    simp only [Fintype.card_prod]
    have hh : 3 * Fintype.card m < Fintype.card n := by omega
    apply Nat.sub_pos_of_lt
    simpa only [Nat.mul_assoc] using Nat.mul_lt_mul_of_pos_right hh ht
  rw [shifted_repeated_block_dimension, balancedDegreeList_sum _ _ hpos,
    balancedDegreeList_length _ _ hpos]
  let r := Fintype.card m - 1
  have hm' : Fintype.card m = r + 1 := by dsimp [r]; omega
  have hn' : Fintype.card n = 4 * r + 3 := by omega
  have hR : Fintype.card (n × t) - 3 * Fintype.card (m × t) = r * Fintype.card t := by
    simp only [Fintype.card_prod, hm', hn']
    have : (4 * r + 3) * Fintype.card t =
        r * Fintype.card t + 3 * ((r + 1) * Fintype.card t) := by ring
    omega
  rw [hR]
  simp only [SLInput, Fintype.card_sum, Fintype.card_prod, hm', hn']
  rw [show 10 * (r + 1) - 1 = 10 * r + 9 by omega]
  ring

end FD56
