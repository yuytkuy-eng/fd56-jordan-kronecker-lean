/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedTwentyOneTangentCriticalBindingBase

/-! A bounded block of exact selected coefficient identities. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

private theorem selected_row0 : ∀ j : Fin 63,
    balancedTwentyOneTangentCriticalSelectedIntegerEntry 0 j%101=(balancedTwentyOneTangentCriticalSelectedData 0 j : ℤ) := by decide +kernel

private theorem selected_row1 : ∀ j : Fin 63,
    balancedTwentyOneTangentCriticalSelectedIntegerEntry 1 j%101=(balancedTwentyOneTangentCriticalSelectedData 1 j : ℤ) := by decide +kernel

private theorem selected_row2 : ∀ j : Fin 63,
    balancedTwentyOneTangentCriticalSelectedIntegerEntry 2 j%101=(balancedTwentyOneTangentCriticalSelectedData 2 j : ℤ) := by decide +kernel

private theorem selected_row3 : ∀ j : Fin 63,
    balancedTwentyOneTangentCriticalSelectedIntegerEntry 3 j%101=(balancedTwentyOneTangentCriticalSelectedData 3 j : ℤ) := by decide +kernel

private theorem selected_row4 : ∀ j : Fin 63,
    balancedTwentyOneTangentCriticalSelectedIntegerEntry 4 j%101=(balancedTwentyOneTangentCriticalSelectedData 4 j : ℤ) := by decide +kernel

private theorem selected_row5 : ∀ j : Fin 63,
    balancedTwentyOneTangentCriticalSelectedIntegerEntry 5 j%101=(balancedTwentyOneTangentCriticalSelectedData 5 j : ℤ) := by decide +kernel

private theorem selected_row6 : ∀ j : Fin 63,
    balancedTwentyOneTangentCriticalSelectedIntegerEntry 6 j%101=(balancedTwentyOneTangentCriticalSelectedData 6 j : ℤ) := by decide +kernel

private theorem selected_row7 : ∀ j : Fin 63,
    balancedTwentyOneTangentCriticalSelectedIntegerEntry 7 j%101=(balancedTwentyOneTangentCriticalSelectedData 7 j : ℤ) := by decide +kernel

private theorem selected_row8 : ∀ j : Fin 63,
    balancedTwentyOneTangentCriticalSelectedIntegerEntry 8 j%101=(balancedTwentyOneTangentCriticalSelectedData 8 j : ℤ) := by decide +kernel

private theorem selected_row9 : ∀ j : Fin 63,
    balancedTwentyOneTangentCriticalSelectedIntegerEntry 9 j%101=(balancedTwentyOneTangentCriticalSelectedData 9 j : ℤ) := by decide +kernel

private theorem selected_row10 : ∀ j : Fin 63,
    balancedTwentyOneTangentCriticalSelectedIntegerEntry 10 j%101=(balancedTwentyOneTangentCriticalSelectedData 10 j : ℤ) := by decide +kernel

private theorem selected_row11 : ∀ j : Fin 63,
    balancedTwentyOneTangentCriticalSelectedIntegerEntry 11 j%101=(balancedTwentyOneTangentCriticalSelectedData 11 j : ℤ) := by decide +kernel

private theorem selected_row12 : ∀ j : Fin 63,
    balancedTwentyOneTangentCriticalSelectedIntegerEntry 12 j%101=(balancedTwentyOneTangentCriticalSelectedData 12 j : ℤ) := by decide +kernel

private theorem selected_row13 : ∀ j : Fin 63,
    balancedTwentyOneTangentCriticalSelectedIntegerEntry 13 j%101=(balancedTwentyOneTangentCriticalSelectedData 13 j : ℤ) := by decide +kernel

private theorem selected_row14 : ∀ j : Fin 63,
    balancedTwentyOneTangentCriticalSelectedIntegerEntry 14 j%101=(balancedTwentyOneTangentCriticalSelectedData 14 j : ℤ) := by decide +kernel

private theorem selected_row15 : ∀ j : Fin 63,
    balancedTwentyOneTangentCriticalSelectedIntegerEntry 15 j%101=(balancedTwentyOneTangentCriticalSelectedData 15 j : ℤ) := by decide +kernel

private theorem selected_row16 : ∀ j : Fin 63,
    balancedTwentyOneTangentCriticalSelectedIntegerEntry 16 j%101=(balancedTwentyOneTangentCriticalSelectedData 16 j : ℤ) := by decide +kernel

private theorem selected_row17 : ∀ j : Fin 63,
    balancedTwentyOneTangentCriticalSelectedIntegerEntry 17 j%101=(balancedTwentyOneTangentCriticalSelectedData 17 j : ℤ) := by decide +kernel

private theorem selected_row18 : ∀ j : Fin 63,
    balancedTwentyOneTangentCriticalSelectedIntegerEntry 18 j%101=(balancedTwentyOneTangentCriticalSelectedData 18 j : ℤ) := by decide +kernel

private theorem selected_row19 : ∀ j : Fin 63,
    balancedTwentyOneTangentCriticalSelectedIntegerEntry 19 j%101=(balancedTwentyOneTangentCriticalSelectedData 19 j : ℤ) := by decide +kernel

theorem balancedTwentyOneTangentCritical_selected_integer_rows_0 (i j : Fin 63)
    (hlo : 0 ≤ i.val) (hhi : i.val < 20) :
    balancedTwentyOneTangentCriticalSelectedIntegerEntry i j%101=(balancedTwentyOneTangentCriticalSelectedData i j : ℤ) := by
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
