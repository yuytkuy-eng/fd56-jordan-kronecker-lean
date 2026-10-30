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

private theorem selected_row40 : ∀ j : Fin 69,
    balancedTwentyFourTangentCriticalSelectedIntegerEntry 40 j%101=(balancedTwentyFourTangentCriticalSelectedData 40 j : ℤ) := by decide +kernel

private theorem selected_row41 : ∀ j : Fin 69,
    balancedTwentyFourTangentCriticalSelectedIntegerEntry 41 j%101=(balancedTwentyFourTangentCriticalSelectedData 41 j : ℤ) := by decide +kernel

private theorem selected_row42 : ∀ j : Fin 69,
    balancedTwentyFourTangentCriticalSelectedIntegerEntry 42 j%101=(balancedTwentyFourTangentCriticalSelectedData 42 j : ℤ) := by decide +kernel

private theorem selected_row43 : ∀ j : Fin 69,
    balancedTwentyFourTangentCriticalSelectedIntegerEntry 43 j%101=(balancedTwentyFourTangentCriticalSelectedData 43 j : ℤ) := by decide +kernel

private theorem selected_row44 : ∀ j : Fin 69,
    balancedTwentyFourTangentCriticalSelectedIntegerEntry 44 j%101=(balancedTwentyFourTangentCriticalSelectedData 44 j : ℤ) := by decide +kernel

private theorem selected_row45 : ∀ j : Fin 69,
    balancedTwentyFourTangentCriticalSelectedIntegerEntry 45 j%101=(balancedTwentyFourTangentCriticalSelectedData 45 j : ℤ) := by decide +kernel

private theorem selected_row46 : ∀ j : Fin 69,
    balancedTwentyFourTangentCriticalSelectedIntegerEntry 46 j%101=(balancedTwentyFourTangentCriticalSelectedData 46 j : ℤ) := by decide +kernel

private theorem selected_row47 : ∀ j : Fin 69,
    balancedTwentyFourTangentCriticalSelectedIntegerEntry 47 j%101=(balancedTwentyFourTangentCriticalSelectedData 47 j : ℤ) := by decide +kernel

private theorem selected_row48 : ∀ j : Fin 69,
    balancedTwentyFourTangentCriticalSelectedIntegerEntry 48 j%101=(balancedTwentyFourTangentCriticalSelectedData 48 j : ℤ) := by decide +kernel

private theorem selected_row49 : ∀ j : Fin 69,
    balancedTwentyFourTangentCriticalSelectedIntegerEntry 49 j%101=(balancedTwentyFourTangentCriticalSelectedData 49 j : ℤ) := by decide +kernel

attribute [local irreducible] balancedTwentyFourTangentCriticalSelectedIntegerEntry balancedTwentyFourTangentCriticalSelectedData

theorem balancedTwentyFourTangentCritical_selected_integer_rows_4 (i j : Fin 69)
    (hlo : 40 ≤ i.val) (hhi : i.val < 50) :
    balancedTwentyFourTangentCriticalSelectedIntegerEntry i j%101=(balancedTwentyFourTangentCriticalSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row40 j
  · exact selected_row41 j
  · exact selected_row42 j
  · exact selected_row43 j
  · exact selected_row44 j
  · exact selected_row45 j
  · exact selected_row46 j
  · exact selected_row47 j
  · exact selected_row48 j
  · exact selected_row49 j

end FD56
