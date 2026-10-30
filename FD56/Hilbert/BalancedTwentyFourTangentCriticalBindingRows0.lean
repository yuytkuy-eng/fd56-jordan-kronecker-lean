/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedTwentyFourTangentCriticalBindingBase

/-! A bounded block of exact selected coefficient identities. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

private theorem selected_row0 : ∀ j : Fin 69,
    balancedTwentyFourTangentCriticalSelectedIntegerEntry 0 j%101=(balancedTwentyFourTangentCriticalSelectedData 0 j : ℤ) := by decide +kernel

private theorem selected_row1 : ∀ j : Fin 69,
    balancedTwentyFourTangentCriticalSelectedIntegerEntry 1 j%101=(balancedTwentyFourTangentCriticalSelectedData 1 j : ℤ) := by decide +kernel

private theorem selected_row2 : ∀ j : Fin 69,
    balancedTwentyFourTangentCriticalSelectedIntegerEntry 2 j%101=(balancedTwentyFourTangentCriticalSelectedData 2 j : ℤ) := by decide +kernel

private theorem selected_row3 : ∀ j : Fin 69,
    balancedTwentyFourTangentCriticalSelectedIntegerEntry 3 j%101=(balancedTwentyFourTangentCriticalSelectedData 3 j : ℤ) := by decide +kernel

private theorem selected_row4 : ∀ j : Fin 69,
    balancedTwentyFourTangentCriticalSelectedIntegerEntry 4 j%101=(balancedTwentyFourTangentCriticalSelectedData 4 j : ℤ) := by decide +kernel

private theorem selected_row5 : ∀ j : Fin 69,
    balancedTwentyFourTangentCriticalSelectedIntegerEntry 5 j%101=(balancedTwentyFourTangentCriticalSelectedData 5 j : ℤ) := by decide +kernel

private theorem selected_row6 : ∀ j : Fin 69,
    balancedTwentyFourTangentCriticalSelectedIntegerEntry 6 j%101=(balancedTwentyFourTangentCriticalSelectedData 6 j : ℤ) := by decide +kernel

private theorem selected_row7 : ∀ j : Fin 69,
    balancedTwentyFourTangentCriticalSelectedIntegerEntry 7 j%101=(balancedTwentyFourTangentCriticalSelectedData 7 j : ℤ) := by decide +kernel

private theorem selected_row8 : ∀ j : Fin 69,
    balancedTwentyFourTangentCriticalSelectedIntegerEntry 8 j%101=(balancedTwentyFourTangentCriticalSelectedData 8 j : ℤ) := by decide +kernel

private theorem selected_row9 : ∀ j : Fin 69,
    balancedTwentyFourTangentCriticalSelectedIntegerEntry 9 j%101=(balancedTwentyFourTangentCriticalSelectedData 9 j : ℤ) := by decide +kernel

attribute [local irreducible] balancedTwentyFourTangentCriticalSelectedIntegerEntry balancedTwentyFourTangentCriticalSelectedData

theorem balancedTwentyFourTangentCritical_selected_integer_rows_0 (i j : Fin 69)
    (hlo : 0 ≤ i.val) (hhi : i.val < 10) :
    balancedTwentyFourTangentCriticalSelectedIntegerEntry i j%101=(balancedTwentyFourTangentCriticalSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row0 j
  · exact selected_row1 j
  · exact selected_row2 j
  · exact selected_row3 j
  · exact selected_row4 j
  · exact selected_row5 j
  · exact selected_row6 j
  · exact selected_row7 j
  · exact selected_row8 j
  · exact selected_row9 j

end FD56
