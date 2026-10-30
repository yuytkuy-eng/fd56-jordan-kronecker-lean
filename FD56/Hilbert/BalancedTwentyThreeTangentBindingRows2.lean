/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedTwentyThreeTangentBindingBase

/-! A bounded block of exact selected coefficient identities. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

private theorem selected_row20 : ∀ j : Fin 60,
    balancedTwentyThreeTangentSelectedIntegerEntry 20 j%101=(balancedTwentyThreeTangentSelectedData 20 j : ℤ) := by decide +kernel

private theorem selected_row21 : ∀ j : Fin 60,
    balancedTwentyThreeTangentSelectedIntegerEntry 21 j%101=(balancedTwentyThreeTangentSelectedData 21 j : ℤ) := by decide +kernel

private theorem selected_row22 : ∀ j : Fin 60,
    balancedTwentyThreeTangentSelectedIntegerEntry 22 j%101=(balancedTwentyThreeTangentSelectedData 22 j : ℤ) := by decide +kernel

private theorem selected_row23 : ∀ j : Fin 60,
    balancedTwentyThreeTangentSelectedIntegerEntry 23 j%101=(balancedTwentyThreeTangentSelectedData 23 j : ℤ) := by decide +kernel

private theorem selected_row24 : ∀ j : Fin 60,
    balancedTwentyThreeTangentSelectedIntegerEntry 24 j%101=(balancedTwentyThreeTangentSelectedData 24 j : ℤ) := by decide +kernel

private theorem selected_row25 : ∀ j : Fin 60,
    balancedTwentyThreeTangentSelectedIntegerEntry 25 j%101=(balancedTwentyThreeTangentSelectedData 25 j : ℤ) := by decide +kernel

private theorem selected_row26 : ∀ j : Fin 60,
    balancedTwentyThreeTangentSelectedIntegerEntry 26 j%101=(balancedTwentyThreeTangentSelectedData 26 j : ℤ) := by decide +kernel

private theorem selected_row27 : ∀ j : Fin 60,
    balancedTwentyThreeTangentSelectedIntegerEntry 27 j%101=(balancedTwentyThreeTangentSelectedData 27 j : ℤ) := by decide +kernel

private theorem selected_row28 : ∀ j : Fin 60,
    balancedTwentyThreeTangentSelectedIntegerEntry 28 j%101=(balancedTwentyThreeTangentSelectedData 28 j : ℤ) := by decide +kernel

private theorem selected_row29 : ∀ j : Fin 60,
    balancedTwentyThreeTangentSelectedIntegerEntry 29 j%101=(balancedTwentyThreeTangentSelectedData 29 j : ℤ) := by decide +kernel

attribute [local irreducible] balancedTwentyThreeTangentSelectedIntegerEntry balancedTwentyThreeTangentSelectedData

theorem balancedTwentyThreeTangent_selected_integer_rows_2 (i j : Fin 60)
    (hlo : 20 ≤ i.val) (hhi : i.val < 30) :
    balancedTwentyThreeTangentSelectedIntegerEntry i j%101=(balancedTwentyThreeTangentSelectedData i j : ℤ) := by
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
