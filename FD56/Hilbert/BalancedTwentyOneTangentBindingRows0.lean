/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedTwentyOneTangentBindingBase

/-! A bounded block of exact selected coefficient identities. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

private theorem selected_row0 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 0 j%101=(balancedTwentyOneTangentSelectedData 0 j : ℤ) := by decide +kernel

private theorem selected_row1 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 1 j%101=(balancedTwentyOneTangentSelectedData 1 j : ℤ) := by decide +kernel

private theorem selected_row2 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 2 j%101=(balancedTwentyOneTangentSelectedData 2 j : ℤ) := by decide +kernel

private theorem selected_row3 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 3 j%101=(balancedTwentyOneTangentSelectedData 3 j : ℤ) := by decide +kernel

private theorem selected_row4 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 4 j%101=(balancedTwentyOneTangentSelectedData 4 j : ℤ) := by decide +kernel

private theorem selected_row5 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 5 j%101=(balancedTwentyOneTangentSelectedData 5 j : ℤ) := by decide +kernel

private theorem selected_row6 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 6 j%101=(balancedTwentyOneTangentSelectedData 6 j : ℤ) := by decide +kernel

private theorem selected_row7 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 7 j%101=(balancedTwentyOneTangentSelectedData 7 j : ℤ) := by decide +kernel

private theorem selected_row8 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 8 j%101=(balancedTwentyOneTangentSelectedData 8 j : ℤ) := by decide +kernel

private theorem selected_row9 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 9 j%101=(balancedTwentyOneTangentSelectedData 9 j : ℤ) := by decide +kernel

private theorem selected_row10 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 10 j%101=(balancedTwentyOneTangentSelectedData 10 j : ℤ) := by decide +kernel

private theorem selected_row11 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 11 j%101=(balancedTwentyOneTangentSelectedData 11 j : ℤ) := by decide +kernel

private theorem selected_row12 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 12 j%101=(balancedTwentyOneTangentSelectedData 12 j : ℤ) := by decide +kernel

private theorem selected_row13 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 13 j%101=(balancedTwentyOneTangentSelectedData 13 j : ℤ) := by decide +kernel

private theorem selected_row14 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 14 j%101=(balancedTwentyOneTangentSelectedData 14 j : ℤ) := by decide +kernel

private theorem selected_row15 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 15 j%101=(balancedTwentyOneTangentSelectedData 15 j : ℤ) := by decide +kernel

private theorem selected_row16 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 16 j%101=(balancedTwentyOneTangentSelectedData 16 j : ℤ) := by decide +kernel

private theorem selected_row17 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 17 j%101=(balancedTwentyOneTangentSelectedData 17 j : ℤ) := by decide +kernel

private theorem selected_row18 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 18 j%101=(balancedTwentyOneTangentSelectedData 18 j : ℤ) := by decide +kernel

private theorem selected_row19 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 19 j%101=(balancedTwentyOneTangentSelectedData 19 j : ℤ) := by decide +kernel

theorem balancedTwentyOneTangent_selected_integer_rows_0 (i j : Fin 60)
    (hlo : 0 ≤ i.val) (hhi : i.val < 20) :
    balancedTwentyOneTangentSelectedIntegerEntry i j%101=(balancedTwentyOneTangentSelectedData i j : ℤ) := by
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
