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

private theorem selected_row60 : ∀ j : Fin 74,
    balancedTwentyFiveTangentCriticalSelectedIntegerEntry 60 j%101=(balancedTwentyFiveTangentCriticalSelectedData 60 j : ℤ) := by decide +kernel

private theorem selected_row61 : ∀ j : Fin 74,
    balancedTwentyFiveTangentCriticalSelectedIntegerEntry 61 j%101=(balancedTwentyFiveTangentCriticalSelectedData 61 j : ℤ) := by decide +kernel

private theorem selected_row62 : ∀ j : Fin 74,
    balancedTwentyFiveTangentCriticalSelectedIntegerEntry 62 j%101=(balancedTwentyFiveTangentCriticalSelectedData 62 j : ℤ) := by decide +kernel

private theorem selected_row63 : ∀ j : Fin 74,
    balancedTwentyFiveTangentCriticalSelectedIntegerEntry 63 j%101=(balancedTwentyFiveTangentCriticalSelectedData 63 j : ℤ) := by decide +kernel

private theorem selected_row64 : ∀ j : Fin 74,
    balancedTwentyFiveTangentCriticalSelectedIntegerEntry 64 j%101=(balancedTwentyFiveTangentCriticalSelectedData 64 j : ℤ) := by decide +kernel

private theorem selected_row65 : ∀ j : Fin 74,
    balancedTwentyFiveTangentCriticalSelectedIntegerEntry 65 j%101=(balancedTwentyFiveTangentCriticalSelectedData 65 j : ℤ) := by decide +kernel

private theorem selected_row66 : ∀ j : Fin 74,
    balancedTwentyFiveTangentCriticalSelectedIntegerEntry 66 j%101=(balancedTwentyFiveTangentCriticalSelectedData 66 j : ℤ) := by decide +kernel

private theorem selected_row67 : ∀ j : Fin 74,
    balancedTwentyFiveTangentCriticalSelectedIntegerEntry 67 j%101=(balancedTwentyFiveTangentCriticalSelectedData 67 j : ℤ) := by decide +kernel

private theorem selected_row68 : ∀ j : Fin 74,
    balancedTwentyFiveTangentCriticalSelectedIntegerEntry 68 j%101=(balancedTwentyFiveTangentCriticalSelectedData 68 j : ℤ) := by decide +kernel

private theorem selected_row69 : ∀ j : Fin 74,
    balancedTwentyFiveTangentCriticalSelectedIntegerEntry 69 j%101=(balancedTwentyFiveTangentCriticalSelectedData 69 j : ℤ) := by decide +kernel

attribute [local irreducible] balancedTwentyFiveTangentCriticalSelectedIntegerEntry balancedTwentyFiveTangentCriticalSelectedData

theorem balancedTwentyFiveTangentCritical_selected_integer_rows_6 (i j : Fin 74)
    (hlo : 60 ≤ i.val) (hhi : i.val < 70) :
    balancedTwentyFiveTangentCriticalSelectedIntegerEntry i j%101=(balancedTwentyFiveTangentCriticalSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row60 j
  · exact selected_row61 j
  · exact selected_row62 j
  · exact selected_row63 j
  · exact selected_row64 j
  · exact selected_row65 j
  · exact selected_row66 j
  · exact selected_row67 j
  · exact selected_row68 j
  · exact selected_row69 j

end FD56
