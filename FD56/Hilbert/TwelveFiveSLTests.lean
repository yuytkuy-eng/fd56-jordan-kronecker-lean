/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericNondivisibleSLStructure
import FD56.Hilbert.MinimalDegreeBudgetTests

/-! The generic twelve-state, five-output SL profile is determined by a
single degree-thirteen vanishing certificate. That certificate remains an
explicit premise in this module. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K : Type*} [Field K]

theorem generic_twelve_five_sl_degrees_of_vanishing (i₀ : Fin 12)
    (hzero : slHilbert (genericAffineSquare K (Fin 12) (Fin 5))
      (genericAffineRows K (Fin 12) (Fin 5)) 13=0) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin 12) (Fin 5))
      (genericAffineRows K (Fin 12) (Fin 5)) i₀) (List.replicate 7 14) := by
  obtain ⟨xs,hlen,hsum,hmin,_⟩ := generic_nondivisible_sl_kronecker_structure
    (K:=K) (n:=Fin 12) (m:=Fin 5) 2 (by decide) i₀ (by decide) (by decide)
  norm_num only [Fintype.card_fin,Nat.reduceMul,Nat.reduceAdd,Nat.reduceSub] at hlen hsum
  have hs : xs.sum=14*7 := by omega
  apply minimal_degrees_uniform_of_budget_test _ xs hmin 14 7 (by decide) (by decide) hlen hs
  rw [← slHilbert_eq_matrix_kernel]
  exact hzero

theorem generic_twelve_five_sl_kronecker_of_vanishing (i₀ : Fin 12)
    (hzero : slHilbert (genericAffineSquare K (Fin 12) (Fin 5))
      (genericAffineRows K (Fin 12) (Fin 5)) 13=0) :
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K (Fin 12) (Fin 5))
      (genericAffineRows K (Fin 12) (Fin 5)) i₀) (List.replicate 7 14) := by
  apply slKirillovMatrix_kronecker _ _ i₀ _
    (genericAffineSquare_degree K _ _) (genericAffineRows_degree K _ _)
    (generic_twelve_five_sl_degrees_of_vanishing i₀ hzero)
  norm_num [slChartInput_card,nat_list_affine_sum,SLInput]

end FD56
