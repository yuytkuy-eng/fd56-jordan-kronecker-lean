/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedTwentyFiveTangentCriticalBindingBase

/-! A bounded block of exact selected coefficient identities. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

private theorem selected_row70 : ∀ j : Fin 74,
    balancedTwentyFiveTangentCriticalSelectedIntegerEntry 70 j%101=(balancedTwentyFiveTangentCriticalSelectedData 70 j : ℤ) := by decide +kernel

private theorem selected_row71 : ∀ j : Fin 74,
    balancedTwentyFiveTangentCriticalSelectedIntegerEntry 71 j%101=(balancedTwentyFiveTangentCriticalSelectedData 71 j : ℤ) := by decide +kernel

private theorem selected_row72 : ∀ j : Fin 74,
    balancedTwentyFiveTangentCriticalSelectedIntegerEntry 72 j%101=(balancedTwentyFiveTangentCriticalSelectedData 72 j : ℤ) := by decide +kernel

private theorem selected_row73 : ∀ j : Fin 74,
    balancedTwentyFiveTangentCriticalSelectedIntegerEntry 73 j%101=(balancedTwentyFiveTangentCriticalSelectedData 73 j : ℤ) := by decide +kernel

attribute [local irreducible] balancedTwentyFiveTangentCriticalSelectedIntegerEntry balancedTwentyFiveTangentCriticalSelectedData

theorem balancedTwentyFiveTangentCritical_selected_integer_rows_7 (i j : Fin 74)
    (hlo : 70 ≤ i.val) (hhi : i.val < 74) :
    balancedTwentyFiveTangentCriticalSelectedIntegerEntry i j%101=(balancedTwentyFiveTangentCriticalSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row70 j
  · exact selected_row71 j
  · exact selected_row72 j
  · exact selected_row73 j

end FD56
