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

private theorem selected_row60 : ∀ j : Fin 67,
    balancedTwentyThreeTangentCriticalSelectedIntegerEntry 60 j%101=(balancedTwentyThreeTangentCriticalSelectedData 60 j : ℤ) := by decide +kernel

private theorem selected_row61 : ∀ j : Fin 67,
    balancedTwentyThreeTangentCriticalSelectedIntegerEntry 61 j%101=(balancedTwentyThreeTangentCriticalSelectedData 61 j : ℤ) := by decide +kernel

private theorem selected_row62 : ∀ j : Fin 67,
    balancedTwentyThreeTangentCriticalSelectedIntegerEntry 62 j%101=(balancedTwentyThreeTangentCriticalSelectedData 62 j : ℤ) := by decide +kernel

private theorem selected_row63 : ∀ j : Fin 67,
    balancedTwentyThreeTangentCriticalSelectedIntegerEntry 63 j%101=(balancedTwentyThreeTangentCriticalSelectedData 63 j : ℤ) := by decide +kernel

private theorem selected_row64 : ∀ j : Fin 67,
    balancedTwentyThreeTangentCriticalSelectedIntegerEntry 64 j%101=(balancedTwentyThreeTangentCriticalSelectedData 64 j : ℤ) := by decide +kernel

private theorem selected_row65 : ∀ j : Fin 67,
    balancedTwentyThreeTangentCriticalSelectedIntegerEntry 65 j%101=(balancedTwentyThreeTangentCriticalSelectedData 65 j : ℤ) := by decide +kernel

private theorem selected_row66 : ∀ j : Fin 67,
    balancedTwentyThreeTangentCriticalSelectedIntegerEntry 66 j%101=(balancedTwentyThreeTangentCriticalSelectedData 66 j : ℤ) := by decide +kernel

attribute [local irreducible] balancedTwentyThreeTangentCriticalSelectedIntegerEntry balancedTwentyThreeTangentCriticalSelectedData

theorem balancedTwentyThreeTangentCritical_selected_integer_rows_6 (i j : Fin 67)
    (hlo : 60 ≤ i.val) (hhi : i.val < 67) :
    balancedTwentyThreeTangentCriticalSelectedIntegerEntry i j%101=(balancedTwentyThreeTangentCriticalSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row60 j
  · exact selected_row61 j
  · exact selected_row62 j
  · exact selected_row63 j
  · exact selected_row64 j
  · exact selected_row65 j
  · exact selected_row66 j

end FD56
