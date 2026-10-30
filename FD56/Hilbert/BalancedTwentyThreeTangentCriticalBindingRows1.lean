/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedTwentyThreeTangentCriticalBindingBase

/-! A bounded block of exact selected coefficient identities. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

private theorem selected_row10 : ∀ j : Fin 67,
    balancedTwentyThreeTangentCriticalSelectedIntegerEntry 10 j%101=(balancedTwentyThreeTangentCriticalSelectedData 10 j : ℤ) := by decide +kernel

private theorem selected_row11 : ∀ j : Fin 67,
    balancedTwentyThreeTangentCriticalSelectedIntegerEntry 11 j%101=(balancedTwentyThreeTangentCriticalSelectedData 11 j : ℤ) := by decide +kernel

private theorem selected_row12 : ∀ j : Fin 67,
    balancedTwentyThreeTangentCriticalSelectedIntegerEntry 12 j%101=(balancedTwentyThreeTangentCriticalSelectedData 12 j : ℤ) := by decide +kernel

private theorem selected_row13 : ∀ j : Fin 67,
    balancedTwentyThreeTangentCriticalSelectedIntegerEntry 13 j%101=(balancedTwentyThreeTangentCriticalSelectedData 13 j : ℤ) := by decide +kernel

private theorem selected_row14 : ∀ j : Fin 67,
    balancedTwentyThreeTangentCriticalSelectedIntegerEntry 14 j%101=(balancedTwentyThreeTangentCriticalSelectedData 14 j : ℤ) := by decide +kernel

private theorem selected_row15 : ∀ j : Fin 67,
    balancedTwentyThreeTangentCriticalSelectedIntegerEntry 15 j%101=(balancedTwentyThreeTangentCriticalSelectedData 15 j : ℤ) := by decide +kernel

private theorem selected_row16 : ∀ j : Fin 67,
    balancedTwentyThreeTangentCriticalSelectedIntegerEntry 16 j%101=(balancedTwentyThreeTangentCriticalSelectedData 16 j : ℤ) := by decide +kernel

private theorem selected_row17 : ∀ j : Fin 67,
    balancedTwentyThreeTangentCriticalSelectedIntegerEntry 17 j%101=(balancedTwentyThreeTangentCriticalSelectedData 17 j : ℤ) := by decide +kernel

private theorem selected_row18 : ∀ j : Fin 67,
    balancedTwentyThreeTangentCriticalSelectedIntegerEntry 18 j%101=(balancedTwentyThreeTangentCriticalSelectedData 18 j : ℤ) := by decide +kernel

private theorem selected_row19 : ∀ j : Fin 67,
    balancedTwentyThreeTangentCriticalSelectedIntegerEntry 19 j%101=(balancedTwentyThreeTangentCriticalSelectedData 19 j : ℤ) := by decide +kernel

attribute [local irreducible] balancedTwentyThreeTangentCriticalSelectedIntegerEntry balancedTwentyThreeTangentCriticalSelectedData

theorem balancedTwentyThreeTangentCritical_selected_integer_rows_1 (i j : Fin 67)
    (hlo : 10 ≤ i.val) (hhi : i.val < 20) :
    balancedTwentyThreeTangentCriticalSelectedIntegerEntry i j%101=(balancedTwentyThreeTangentCriticalSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row10 j
  · exact selected_row11 j
  · exact selected_row12 j
  · exact selected_row13 j
  · exact selected_row14 j
  · exact selected_row15 j
  · exact selected_row16 j
  · exact selected_row17 j
  · exact selected_row18 j
  · exact selected_row19 j

end FD56
