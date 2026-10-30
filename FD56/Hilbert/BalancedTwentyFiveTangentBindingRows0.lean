/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedTwentyFiveTangentBindingBase

/-! A bounded block of exact selected coefficient identities. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

private theorem selected_row0 : ∀ j : Fin 70,
    balancedTwentyFiveTangentSelectedIntegerEntry 0 j%101=(balancedTwentyFiveTangentSelectedData 0 j : ℤ) := by decide +kernel

private theorem selected_row1 : ∀ j : Fin 70,
    balancedTwentyFiveTangentSelectedIntegerEntry 1 j%101=(balancedTwentyFiveTangentSelectedData 1 j : ℤ) := by decide +kernel

private theorem selected_row2 : ∀ j : Fin 70,
    balancedTwentyFiveTangentSelectedIntegerEntry 2 j%101=(balancedTwentyFiveTangentSelectedData 2 j : ℤ) := by decide +kernel

private theorem selected_row3 : ∀ j : Fin 70,
    balancedTwentyFiveTangentSelectedIntegerEntry 3 j%101=(balancedTwentyFiveTangentSelectedData 3 j : ℤ) := by decide +kernel

private theorem selected_row4 : ∀ j : Fin 70,
    balancedTwentyFiveTangentSelectedIntegerEntry 4 j%101=(balancedTwentyFiveTangentSelectedData 4 j : ℤ) := by decide +kernel

private theorem selected_row5 : ∀ j : Fin 70,
    balancedTwentyFiveTangentSelectedIntegerEntry 5 j%101=(balancedTwentyFiveTangentSelectedData 5 j : ℤ) := by decide +kernel

private theorem selected_row6 : ∀ j : Fin 70,
    balancedTwentyFiveTangentSelectedIntegerEntry 6 j%101=(balancedTwentyFiveTangentSelectedData 6 j : ℤ) := by decide +kernel

private theorem selected_row7 : ∀ j : Fin 70,
    balancedTwentyFiveTangentSelectedIntegerEntry 7 j%101=(balancedTwentyFiveTangentSelectedData 7 j : ℤ) := by decide +kernel

private theorem selected_row8 : ∀ j : Fin 70,
    balancedTwentyFiveTangentSelectedIntegerEntry 8 j%101=(balancedTwentyFiveTangentSelectedData 8 j : ℤ) := by decide +kernel

private theorem selected_row9 : ∀ j : Fin 70,
    balancedTwentyFiveTangentSelectedIntegerEntry 9 j%101=(balancedTwentyFiveTangentSelectedData 9 j : ℤ) := by decide +kernel

attribute [local irreducible] balancedTwentyFiveTangentSelectedIntegerEntry balancedTwentyFiveTangentSelectedData

theorem balancedTwentyFiveTangent_selected_integer_rows_0 (i j : Fin 70)
    (hlo : 0 ≤ i.val) (hhi : i.val < 10) :
    balancedTwentyFiveTangentSelectedIntegerEntry i j%101=(balancedTwentyFiveTangentSelectedData i j : ℤ) := by
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
