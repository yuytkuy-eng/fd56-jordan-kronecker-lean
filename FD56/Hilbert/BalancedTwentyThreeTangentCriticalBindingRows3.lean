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

private theorem selected_row30 : ∀ j : Fin 67,
    balancedTwentyThreeTangentCriticalSelectedIntegerEntry 30 j%101=(balancedTwentyThreeTangentCriticalSelectedData 30 j : ℤ) := by decide +kernel

private theorem selected_row31 : ∀ j : Fin 67,
    balancedTwentyThreeTangentCriticalSelectedIntegerEntry 31 j%101=(balancedTwentyThreeTangentCriticalSelectedData 31 j : ℤ) := by decide +kernel

private theorem selected_row32 : ∀ j : Fin 67,
    balancedTwentyThreeTangentCriticalSelectedIntegerEntry 32 j%101=(balancedTwentyThreeTangentCriticalSelectedData 32 j : ℤ) := by decide +kernel

private theorem selected_row33 : ∀ j : Fin 67,
    balancedTwentyThreeTangentCriticalSelectedIntegerEntry 33 j%101=(balancedTwentyThreeTangentCriticalSelectedData 33 j : ℤ) := by decide +kernel

private theorem selected_row34 : ∀ j : Fin 67,
    balancedTwentyThreeTangentCriticalSelectedIntegerEntry 34 j%101=(balancedTwentyThreeTangentCriticalSelectedData 34 j : ℤ) := by decide +kernel

private theorem selected_row35 : ∀ j : Fin 67,
    balancedTwentyThreeTangentCriticalSelectedIntegerEntry 35 j%101=(balancedTwentyThreeTangentCriticalSelectedData 35 j : ℤ) := by decide +kernel

private theorem selected_row36 : ∀ j : Fin 67,
    balancedTwentyThreeTangentCriticalSelectedIntegerEntry 36 j%101=(balancedTwentyThreeTangentCriticalSelectedData 36 j : ℤ) := by decide +kernel

private theorem selected_row37 : ∀ j : Fin 67,
    balancedTwentyThreeTangentCriticalSelectedIntegerEntry 37 j%101=(balancedTwentyThreeTangentCriticalSelectedData 37 j : ℤ) := by decide +kernel

private theorem selected_row38 : ∀ j : Fin 67,
    balancedTwentyThreeTangentCriticalSelectedIntegerEntry 38 j%101=(balancedTwentyThreeTangentCriticalSelectedData 38 j : ℤ) := by decide +kernel

private theorem selected_row39 : ∀ j : Fin 67,
    balancedTwentyThreeTangentCriticalSelectedIntegerEntry 39 j%101=(balancedTwentyThreeTangentCriticalSelectedData 39 j : ℤ) := by decide +kernel

attribute [local irreducible] balancedTwentyThreeTangentCriticalSelectedIntegerEntry balancedTwentyThreeTangentCriticalSelectedData

theorem balancedTwentyThreeTangentCritical_selected_integer_rows_3 (i j : Fin 67)
    (hlo : 30 ≤ i.val) (hhi : i.val < 40) :
    balancedTwentyThreeTangentCriticalSelectedIntegerEntry i j%101=(balancedTwentyThreeTangentCriticalSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row30 j
  · exact selected_row31 j
  · exact selected_row32 j
  · exact selected_row33 j
  · exact selected_row34 j
  · exact selected_row35 j
  · exact selected_row36 j
  · exact selected_row37 j
  · exact selected_row38 j
  · exact selected_row39 j

end FD56
