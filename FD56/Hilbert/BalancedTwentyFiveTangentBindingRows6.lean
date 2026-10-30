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

private theorem selected_row60 : ∀ j : Fin 70,
    balancedTwentyFiveTangentSelectedIntegerEntry 60 j%101=(balancedTwentyFiveTangentSelectedData 60 j : ℤ) := by decide +kernel

private theorem selected_row61 : ∀ j : Fin 70,
    balancedTwentyFiveTangentSelectedIntegerEntry 61 j%101=(balancedTwentyFiveTangentSelectedData 61 j : ℤ) := by decide +kernel

private theorem selected_row62 : ∀ j : Fin 70,
    balancedTwentyFiveTangentSelectedIntegerEntry 62 j%101=(balancedTwentyFiveTangentSelectedData 62 j : ℤ) := by decide +kernel

private theorem selected_row63 : ∀ j : Fin 70,
    balancedTwentyFiveTangentSelectedIntegerEntry 63 j%101=(balancedTwentyFiveTangentSelectedData 63 j : ℤ) := by decide +kernel

private theorem selected_row64 : ∀ j : Fin 70,
    balancedTwentyFiveTangentSelectedIntegerEntry 64 j%101=(balancedTwentyFiveTangentSelectedData 64 j : ℤ) := by decide +kernel

private theorem selected_row65 : ∀ j : Fin 70,
    balancedTwentyFiveTangentSelectedIntegerEntry 65 j%101=(balancedTwentyFiveTangentSelectedData 65 j : ℤ) := by decide +kernel

private theorem selected_row66 : ∀ j : Fin 70,
    balancedTwentyFiveTangentSelectedIntegerEntry 66 j%101=(balancedTwentyFiveTangentSelectedData 66 j : ℤ) := by decide +kernel

private theorem selected_row67 : ∀ j : Fin 70,
    balancedTwentyFiveTangentSelectedIntegerEntry 67 j%101=(balancedTwentyFiveTangentSelectedData 67 j : ℤ) := by decide +kernel

private theorem selected_row68 : ∀ j : Fin 70,
    balancedTwentyFiveTangentSelectedIntegerEntry 68 j%101=(balancedTwentyFiveTangentSelectedData 68 j : ℤ) := by decide +kernel

private theorem selected_row69 : ∀ j : Fin 70,
    balancedTwentyFiveTangentSelectedIntegerEntry 69 j%101=(balancedTwentyFiveTangentSelectedData 69 j : ℤ) := by decide +kernel

attribute [local irreducible] balancedTwentyFiveTangentSelectedIntegerEntry balancedTwentyFiveTangentSelectedData

theorem balancedTwentyFiveTangent_selected_integer_rows_6 (i j : Fin 70)
    (hlo : 60 ≤ i.val) (hhi : i.val < 70) :
    balancedTwentyFiveTangentSelectedIntegerEntry i j%101=(balancedTwentyFiveTangentSelectedData i j : ℤ) := by
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
