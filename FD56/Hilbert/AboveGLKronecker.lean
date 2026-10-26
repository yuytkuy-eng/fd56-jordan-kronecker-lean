/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MixedGLKronecker

/-! The full generic GL pencil above the square range is a sum of Kronecker blocks. -/

noncomputable section
namespace FD56
open Matrix Polynomial

theorem above_gl_kronecker_dimension (n m : ℕ) (h : n < m) :
    ((List.replicate (n * (n % (m - n))) (n / (m - n) + 1) ++
      List.replicate (n * ((m - n) - n % (m - n))) (n / (m - n))).map
        (fun e => 2 * e + 1)).sum = n * n + n * m := by
  let s := m - n
  have hs : 0 < s := by dsimp [s]; omega
  have hm : m = n + s := by dsimp [s]; omega
  have hv : n % s < s := Nat.mod_lt n hs
  have hq : n % s + s * (n / s) = n := Nat.mod_add_div n s
  have hw : s - n % s + n % s = s := by omega
  change ((List.replicate (n * (n % s)) (n / s + 1) ++
    List.replicate (n * (s - n % s)) (n / s)).map (fun e => 2 * e + 1)).sum = _
  simp only [List.map_append, List.map_replicate, List.sum_append, List.sum_replicate,
    smul_eq_mul]
  calc
    n * (n % s) * (2 * (n / s + 1) + 1) + n * (s - n % s) * (2 * (n / s) + 1) =
        n * (2 * (n % s + ((s - n % s) + n % s) * (n / s)) +
          ((s - n % s) + n % s)) := by ring
    _ = n * n + n * m := by rw [hw, hq, hm]; ring

variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem generic_above_gl_kronecker_decomposition (hnm : Fintype.card n < Fintype.card m) :
    HasKroneckerDecomposition (glKirillovMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m))
      (List.replicate (Fintype.card n * (Fintype.card n % (Fintype.card m - Fintype.card n)))
        (Fintype.card n / (Fintype.card m - Fintype.card n) + 1) ++
      List.replicate (Fintype.card n * ((Fintype.card m - Fintype.card n) -
        Fintype.card n % (Fintype.card m - Fintype.card n)))
        (Fintype.card n / (Fintype.card m - Fintype.card n))) := by
  apply glKirillovMatrix_kronecker _ _ _
    (genericAffineSquare_degree K _ _) (genericAffineRows_degree K _ _)
    (generic_above_gl_minimal_degrees hnm)
  rw [above_gl_kronecker_dimension _ _ hnm]
  simp only [SLInput, Fintype.card_sum, Fintype.card_prod]

end FD56
