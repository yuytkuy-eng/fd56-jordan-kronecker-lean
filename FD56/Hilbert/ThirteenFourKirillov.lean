/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GLKirillovPencil
import FD56.Hilbert.DepthThreeThirteenFourFamily

/-! Minimal degrees and the dimension budget for the thirteen/four Kirillov family.
These statements do not construct a constant congruence to canonical blocks. -/

namespace FD56
open Matrix Polynomial

variable {K t : Type*} [Field K] [CharZero K] [Fintype t] [DecidableEq t] [Nonempty t]

theorem generic_thirteen_four_repeated_kirillov_minimal_degrees :
    HasMinimalKernelDegrees (glKirillovMatrix
      (genericAffineSquare K (Fin 13 × t) (Fin 4 × t))
      (genericAffineRows K (Fin 13 × t) (Fin 4 × t)))
      (List.replicate (2 * Fintype.card t ^ 2) 36 ++
        List.replicate (Fintype.card t ^ 2) 37) := by
  apply (glKirillovMatrix_hasMinimalKernelDegrees_iff _ _ _).mpr
  exact generic_thirteen_four_repeated_gl_minimal_degrees

omit [Field K] [CharZero K] [DecidableEq t] [Nonempty t] in
theorem thirteen_four_repeated_kirillov_dimension_budget :
    (((List.replicate (2 * Fintype.card t ^ 2) 36 ++
      List.replicate (Fintype.card t ^ 2) 37)).map (fun e => 2 * e + 1)).sum =
      Fintype.card (SLInput (Fin 13 × t) (Fin 4 × t)) := by
  simp only [List.map_append, List.map_replicate, List.sum_append,
    List.sum_replicate, smul_eq_mul, SLInput, Fintype.card_sum,
    Fintype.card_prod, Fintype.card_fin]
  ring

end FD56
