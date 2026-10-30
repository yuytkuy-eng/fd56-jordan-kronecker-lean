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

private theorem selected_row20 : ∀ j : Fin 74,
    balancedTwentyFiveTangentCriticalSelectedIntegerEntry 20 j%101=(balancedTwentyFiveTangentCriticalSelectedData 20 j : ℤ) := by decide +kernel

private theorem selected_row21 : ∀ j : Fin 74,
    balancedTwentyFiveTangentCriticalSelectedIntegerEntry 21 j%101=(balancedTwentyFiveTangentCriticalSelectedData 21 j : ℤ) := by decide +kernel

private theorem selected_row22 : ∀ j : Fin 74,
    balancedTwentyFiveTangentCriticalSelectedIntegerEntry 22 j%101=(balancedTwentyFiveTangentCriticalSelectedData 22 j : ℤ) := by decide +kernel

private theorem selected_row23 : ∀ j : Fin 74,
    balancedTwentyFiveTangentCriticalSelectedIntegerEntry 23 j%101=(balancedTwentyFiveTangentCriticalSelectedData 23 j : ℤ) := by decide +kernel

private theorem selected_row24 : ∀ j : Fin 74,
    balancedTwentyFiveTangentCriticalSelectedIntegerEntry 24 j%101=(balancedTwentyFiveTangentCriticalSelectedData 24 j : ℤ) := by decide +kernel

private theorem selected_row25 : ∀ j : Fin 74,
    balancedTwentyFiveTangentCriticalSelectedIntegerEntry 25 j%101=(balancedTwentyFiveTangentCriticalSelectedData 25 j : ℤ) := by decide +kernel

private theorem selected_row26 : ∀ j : Fin 74,
    balancedTwentyFiveTangentCriticalSelectedIntegerEntry 26 j%101=(balancedTwentyFiveTangentCriticalSelectedData 26 j : ℤ) := by decide +kernel

private theorem selected_row27 : ∀ j : Fin 74,
    balancedTwentyFiveTangentCriticalSelectedIntegerEntry 27 j%101=(balancedTwentyFiveTangentCriticalSelectedData 27 j : ℤ) := by decide +kernel

private theorem selected_row28 : ∀ j : Fin 74,
    balancedTwentyFiveTangentCriticalSelectedIntegerEntry 28 j%101=(balancedTwentyFiveTangentCriticalSelectedData 28 j : ℤ) := by decide +kernel

private theorem selected_row29 : ∀ j : Fin 74,
    balancedTwentyFiveTangentCriticalSelectedIntegerEntry 29 j%101=(balancedTwentyFiveTangentCriticalSelectedData 29 j : ℤ) := by decide +kernel

attribute [local irreducible] balancedTwentyFiveTangentCriticalSelectedIntegerEntry balancedTwentyFiveTangentCriticalSelectedData

theorem balancedTwentyFiveTangentCritical_selected_integer_rows_2 (i j : Fin 74)
    (hlo : 20 ≤ i.val) (hhi : i.val < 30) :
    balancedTwentyFiveTangentCriticalSelectedIntegerEntry i j%101=(balancedTwentyFiveTangentCriticalSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row20 j
  · exact selected_row21 j
  · exact selected_row22 j
  · exact selected_row23 j
  · exact selected_row24 j
  · exact selected_row25 j
  · exact selected_row26 j
  · exact selected_row27 j
  · exact selected_row28 j
  · exact selected_row29 j

end FD56
