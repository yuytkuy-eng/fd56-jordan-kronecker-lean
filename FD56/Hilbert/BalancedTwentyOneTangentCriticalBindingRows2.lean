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

private theorem selected_row40 : ∀ j : Fin 63,
    balancedTwentyOneTangentCriticalSelectedIntegerEntry 40 j%101=(balancedTwentyOneTangentCriticalSelectedData 40 j : ℤ) := by decide +kernel

private theorem selected_row41 : ∀ j : Fin 63,
    balancedTwentyOneTangentCriticalSelectedIntegerEntry 41 j%101=(balancedTwentyOneTangentCriticalSelectedData 41 j : ℤ) := by decide +kernel

private theorem selected_row42 : ∀ j : Fin 63,
    balancedTwentyOneTangentCriticalSelectedIntegerEntry 42 j%101=(balancedTwentyOneTangentCriticalSelectedData 42 j : ℤ) := by decide +kernel

private theorem selected_row43 : ∀ j : Fin 63,
    balancedTwentyOneTangentCriticalSelectedIntegerEntry 43 j%101=(balancedTwentyOneTangentCriticalSelectedData 43 j : ℤ) := by decide +kernel

private theorem selected_row44 : ∀ j : Fin 63,
    balancedTwentyOneTangentCriticalSelectedIntegerEntry 44 j%101=(balancedTwentyOneTangentCriticalSelectedData 44 j : ℤ) := by decide +kernel

private theorem selected_row45 : ∀ j : Fin 63,
    balancedTwentyOneTangentCriticalSelectedIntegerEntry 45 j%101=(balancedTwentyOneTangentCriticalSelectedData 45 j : ℤ) := by decide +kernel

private theorem selected_row46 : ∀ j : Fin 63,
    balancedTwentyOneTangentCriticalSelectedIntegerEntry 46 j%101=(balancedTwentyOneTangentCriticalSelectedData 46 j : ℤ) := by decide +kernel

private theorem selected_row47 : ∀ j : Fin 63,
    balancedTwentyOneTangentCriticalSelectedIntegerEntry 47 j%101=(balancedTwentyOneTangentCriticalSelectedData 47 j : ℤ) := by decide +kernel

private theorem selected_row48 : ∀ j : Fin 63,
    balancedTwentyOneTangentCriticalSelectedIntegerEntry 48 j%101=(balancedTwentyOneTangentCriticalSelectedData 48 j : ℤ) := by decide +kernel

private theorem selected_row49 : ∀ j : Fin 63,
    balancedTwentyOneTangentCriticalSelectedIntegerEntry 49 j%101=(balancedTwentyOneTangentCriticalSelectedData 49 j : ℤ) := by decide +kernel

private theorem selected_row50 : ∀ j : Fin 63,
    balancedTwentyOneTangentCriticalSelectedIntegerEntry 50 j%101=(balancedTwentyOneTangentCriticalSelectedData 50 j : ℤ) := by decide +kernel

private theorem selected_row51 : ∀ j : Fin 63,
    balancedTwentyOneTangentCriticalSelectedIntegerEntry 51 j%101=(balancedTwentyOneTangentCriticalSelectedData 51 j : ℤ) := by decide +kernel

private theorem selected_row52 : ∀ j : Fin 63,
    balancedTwentyOneTangentCriticalSelectedIntegerEntry 52 j%101=(balancedTwentyOneTangentCriticalSelectedData 52 j : ℤ) := by decide +kernel

private theorem selected_row53 : ∀ j : Fin 63,
    balancedTwentyOneTangentCriticalSelectedIntegerEntry 53 j%101=(balancedTwentyOneTangentCriticalSelectedData 53 j : ℤ) := by decide +kernel

private theorem selected_row54 : ∀ j : Fin 63,
    balancedTwentyOneTangentCriticalSelectedIntegerEntry 54 j%101=(balancedTwentyOneTangentCriticalSelectedData 54 j : ℤ) := by decide +kernel

private theorem selected_row55 : ∀ j : Fin 63,
    balancedTwentyOneTangentCriticalSelectedIntegerEntry 55 j%101=(balancedTwentyOneTangentCriticalSelectedData 55 j : ℤ) := by decide +kernel

private theorem selected_row56 : ∀ j : Fin 63,
    balancedTwentyOneTangentCriticalSelectedIntegerEntry 56 j%101=(balancedTwentyOneTangentCriticalSelectedData 56 j : ℤ) := by decide +kernel

private theorem selected_row57 : ∀ j : Fin 63,
    balancedTwentyOneTangentCriticalSelectedIntegerEntry 57 j%101=(balancedTwentyOneTangentCriticalSelectedData 57 j : ℤ) := by decide +kernel

private theorem selected_row58 : ∀ j : Fin 63,
    balancedTwentyOneTangentCriticalSelectedIntegerEntry 58 j%101=(balancedTwentyOneTangentCriticalSelectedData 58 j : ℤ) := by decide +kernel

private theorem selected_row59 : ∀ j : Fin 63,
    balancedTwentyOneTangentCriticalSelectedIntegerEntry 59 j%101=(balancedTwentyOneTangentCriticalSelectedData 59 j : ℤ) := by decide +kernel

theorem balancedTwentyOneTangentCritical_selected_integer_rows_2 (i j : Fin 63)
    (hlo : 40 ≤ i.val) (hhi : i.val < 60) :
    balancedTwentyOneTangentCriticalSelectedIntegerEntry i j%101=(balancedTwentyOneTangentCriticalSelectedData i j : ℤ) := by
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
