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

private theorem selected_row50 : ∀ j : Fin 69,
    balancedTwentyFourTangentCriticalSelectedIntegerEntry 50 j%101=(balancedTwentyFourTangentCriticalSelectedData 50 j : ℤ) := by decide +kernel

private theorem selected_row51 : ∀ j : Fin 69,
    balancedTwentyFourTangentCriticalSelectedIntegerEntry 51 j%101=(balancedTwentyFourTangentCriticalSelectedData 51 j : ℤ) := by decide +kernel

private theorem selected_row52 : ∀ j : Fin 69,
    balancedTwentyFourTangentCriticalSelectedIntegerEntry 52 j%101=(balancedTwentyFourTangentCriticalSelectedData 52 j : ℤ) := by decide +kernel

private theorem selected_row53 : ∀ j : Fin 69,
    balancedTwentyFourTangentCriticalSelectedIntegerEntry 53 j%101=(balancedTwentyFourTangentCriticalSelectedData 53 j : ℤ) := by decide +kernel

private theorem selected_row54 : ∀ j : Fin 69,
    balancedTwentyFourTangentCriticalSelectedIntegerEntry 54 j%101=(balancedTwentyFourTangentCriticalSelectedData 54 j : ℤ) := by decide +kernel

private theorem selected_row55 : ∀ j : Fin 69,
    balancedTwentyFourTangentCriticalSelectedIntegerEntry 55 j%101=(balancedTwentyFourTangentCriticalSelectedData 55 j : ℤ) := by decide +kernel

private theorem selected_row56 : ∀ j : Fin 69,
    balancedTwentyFourTangentCriticalSelectedIntegerEntry 56 j%101=(balancedTwentyFourTangentCriticalSelectedData 56 j : ℤ) := by decide +kernel

private theorem selected_row57 : ∀ j : Fin 69,
    balancedTwentyFourTangentCriticalSelectedIntegerEntry 57 j%101=(balancedTwentyFourTangentCriticalSelectedData 57 j : ℤ) := by decide +kernel

private theorem selected_row58 : ∀ j : Fin 69,
    balancedTwentyFourTangentCriticalSelectedIntegerEntry 58 j%101=(balancedTwentyFourTangentCriticalSelectedData 58 j : ℤ) := by decide +kernel

private theorem selected_row59 : ∀ j : Fin 69,
    balancedTwentyFourTangentCriticalSelectedIntegerEntry 59 j%101=(balancedTwentyFourTangentCriticalSelectedData 59 j : ℤ) := by decide +kernel

attribute [local irreducible] balancedTwentyFourTangentCriticalSelectedIntegerEntry balancedTwentyFourTangentCriticalSelectedData

theorem balancedTwentyFourTangentCritical_selected_integer_rows_5 (i j : Fin 69)
    (hlo : 50 ≤ i.val) (hhi : i.val < 60) :
    balancedTwentyFourTangentCriticalSelectedIntegerEntry i j%101=(balancedTwentyFourTangentCriticalSelectedData i j : ℤ) := by
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
