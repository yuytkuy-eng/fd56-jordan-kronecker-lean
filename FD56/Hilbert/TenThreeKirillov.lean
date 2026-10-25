/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GLKirillovPencil
import FD56.Hilbert.DepthThreeTenThreeFamily

/-! Minimal degrees and the dimension budget for the ten/three Kirillov family.
These statements do not construct a constant congruence to canonical blocks. -/

namespace FD56
open Matrix Polynomial

variable {K t : Type*} [Field K] [CharZero K] [Fintype t] [DecidableEq t] [Nonempty t]

theorem generic_ten_three_repeated_kirillov_minimal_degrees :
    HasMinimalKernelDegrees (glKirillovMatrix
      (genericAffineSquare K (Fin 10 × t) (Fin 3 × t))
      (genericAffineRows K (Fin 10 × t) (Fin 3 × t)))
      (List.replicate (2 * Fintype.card t ^ 2) 32) := by
  apply (glKirillovMatrix_hasMinimalKernelDegrees_iff _ _ _).mpr
  exact generic_ten_three_repeated_gl_minimal_degrees

omit [Field K] [CharZero K] [DecidableEq t] [Nonempty t] in
theorem ten_three_repeated_kirillov_dimension_budget :
    ((List.replicate (2 * Fintype.card t ^ 2) 32).map (fun e => 2 * e + 1)).sum =
      Fintype.card (SLInput (Fin 10 × t) (Fin 3 × t)) := by
  simp only [List.map_replicate, List.sum_replicate, smul_eq_mul,
    SLInput, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  ring

end FD56
