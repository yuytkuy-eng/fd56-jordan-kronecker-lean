/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedTwentyFourTangentBindingBase

/-! A bounded block of exact selected coefficient identities. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

private theorem selected_row50 : ∀ j : Fin 60,
    balancedTwentyFourTangentSelectedIntegerEntry 50 j%101=(balancedTwentyFourTangentSelectedData 50 j : ℤ) := by decide +kernel

private theorem selected_row51 : ∀ j : Fin 60,
    balancedTwentyFourTangentSelectedIntegerEntry 51 j%101=(balancedTwentyFourTangentSelectedData 51 j : ℤ) := by decide +kernel

private theorem selected_row52 : ∀ j : Fin 60,
    balancedTwentyFourTangentSelectedIntegerEntry 52 j%101=(balancedTwentyFourTangentSelectedData 52 j : ℤ) := by decide +kernel

private theorem selected_row53 : ∀ j : Fin 60,
    balancedTwentyFourTangentSelectedIntegerEntry 53 j%101=(balancedTwentyFourTangentSelectedData 53 j : ℤ) := by decide +kernel

private theorem selected_row54 : ∀ j : Fin 60,
    balancedTwentyFourTangentSelectedIntegerEntry 54 j%101=(balancedTwentyFourTangentSelectedData 54 j : ℤ) := by decide +kernel

private theorem selected_row55 : ∀ j : Fin 60,
    balancedTwentyFourTangentSelectedIntegerEntry 55 j%101=(balancedTwentyFourTangentSelectedData 55 j : ℤ) := by decide +kernel

private theorem selected_row56 : ∀ j : Fin 60,
    balancedTwentyFourTangentSelectedIntegerEntry 56 j%101=(balancedTwentyFourTangentSelectedData 56 j : ℤ) := by decide +kernel

private theorem selected_row57 : ∀ j : Fin 60,
    balancedTwentyFourTangentSelectedIntegerEntry 57 j%101=(balancedTwentyFourTangentSelectedData 57 j : ℤ) := by decide +kernel

private theorem selected_row58 : ∀ j : Fin 60,
    balancedTwentyFourTangentSelectedIntegerEntry 58 j%101=(balancedTwentyFourTangentSelectedData 58 j : ℤ) := by decide +kernel

private theorem selected_row59 : ∀ j : Fin 60,
    balancedTwentyFourTangentSelectedIntegerEntry 59 j%101=(balancedTwentyFourTangentSelectedData 59 j : ℤ) := by decide +kernel

attribute [local irreducible] balancedTwentyFourTangentSelectedIntegerEntry balancedTwentyFourTangentSelectedData

theorem balancedTwentyFourTangent_selected_integer_rows_5 (i j : Fin 60)
    (hlo : 50 ≤ i.val) (hhi : i.val < 60) :
    balancedTwentyFourTangentSelectedIntegerEntry i j%101=(balancedTwentyFourTangentSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row50 j
  · exact selected_row51 j
  · exact selected_row52 j
  · exact selected_row53 j
  · exact selected_row54 j
  · exact selected_row55 j
  · exact selected_row56 j
  · exact selected_row57 j
  · exact selected_row58 j
  · exact selected_row59 j

end FD56
