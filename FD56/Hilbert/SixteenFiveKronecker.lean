/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthThreeSixteenFiveFamily
import FD56.Hilbert.MixedGLKronecker

/-! Canonical Kronecker blocks for the characteristic-zero sixteen/five family. -/

noncomputable section
namespace FD56
open Matrix Polynomial

theorem sixteen_five_repeated_kirillov_dimension_budget
    {t : Type*} [Fintype t] :
    ((List.replicate (2 * Fintype.card t ^ 2) 41 ++
      List.replicate (2 * Fintype.card t ^ 2) 42).map (fun e => 2*e+1)).sum =
        Fintype.card (SLInput (Fin 16 × t) (Fin 5 × t)) := by
  simp only [List.map_append,List.map_replicate,List.sum_append,List.sum_replicate,
    smul_eq_mul,SLInput,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  ring

theorem generic_sixteen_five_repeated_gl_kronecker_decomposition
    {K t : Type*} [Field K] [CharZero K] [Fintype t] [DecidableEq t] [Nonempty t] :
    HasKroneckerDecomposition (glKirillovMatrix
      (genericAffineSquare K (Fin 16 × t) (Fin 5 × t))
      (genericAffineRows K (Fin 16 × t) (Fin 5 × t)))
      (List.replicate (2 * Fintype.card t ^ 2) 41 ++
        List.replicate (2 * Fintype.card t ^ 2) 42) := by
  exact glKirillovMatrix_kronecker _ _ _
    (genericAffineSquare_degree K _ _) (genericAffineRows_degree K _ _)
    generic_sixteen_five_repeated_gl_minimal_degrees
    sixteen_five_repeated_kirillov_dimension_budget.symm

end FD56
