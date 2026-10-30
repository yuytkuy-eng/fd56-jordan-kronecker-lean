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

private theorem selected_row60 : ∀ j : Fin 69,
    balancedTwentyFourTangentCriticalSelectedIntegerEntry 60 j%101=(balancedTwentyFourTangentCriticalSelectedData 60 j : ℤ) := by decide +kernel

private theorem selected_row61 : ∀ j : Fin 69,
    balancedTwentyFourTangentCriticalSelectedIntegerEntry 61 j%101=(balancedTwentyFourTangentCriticalSelectedData 61 j : ℤ) := by decide +kernel

private theorem selected_row62 : ∀ j : Fin 69,
    balancedTwentyFourTangentCriticalSelectedIntegerEntry 62 j%101=(balancedTwentyFourTangentCriticalSelectedData 62 j : ℤ) := by decide +kernel

private theorem selected_row63 : ∀ j : Fin 69,
    balancedTwentyFourTangentCriticalSelectedIntegerEntry 63 j%101=(balancedTwentyFourTangentCriticalSelectedData 63 j : ℤ) := by decide +kernel

private theorem selected_row64 : ∀ j : Fin 69,
    balancedTwentyFourTangentCriticalSelectedIntegerEntry 64 j%101=(balancedTwentyFourTangentCriticalSelectedData 64 j : ℤ) := by decide +kernel

private theorem selected_row65 : ∀ j : Fin 69,
    balancedTwentyFourTangentCriticalSelectedIntegerEntry 65 j%101=(balancedTwentyFourTangentCriticalSelectedData 65 j : ℤ) := by decide +kernel

private theorem selected_row66 : ∀ j : Fin 69,
    balancedTwentyFourTangentCriticalSelectedIntegerEntry 66 j%101=(balancedTwentyFourTangentCriticalSelectedData 66 j : ℤ) := by decide +kernel

private theorem selected_row67 : ∀ j : Fin 69,
    balancedTwentyFourTangentCriticalSelectedIntegerEntry 67 j%101=(balancedTwentyFourTangentCriticalSelectedData 67 j : ℤ) := by decide +kernel

private theorem selected_row68 : ∀ j : Fin 69,
    balancedTwentyFourTangentCriticalSelectedIntegerEntry 68 j%101=(balancedTwentyFourTangentCriticalSelectedData 68 j : ℤ) := by decide +kernel

attribute [local irreducible] balancedTwentyFourTangentCriticalSelectedIntegerEntry balancedTwentyFourTangentCriticalSelectedData

theorem balancedTwentyFourTangentCritical_selected_integer_rows_6 (i j : Fin 69)
    (hlo : 60 ≤ i.val) (hhi : i.val < 69) :
    balancedTwentyFourTangentCriticalSelectedIntegerEntry i j%101=(balancedTwentyFourTangentCriticalSelectedData i j : ℤ) := by
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

end FD56
