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

private theorem selected_row40 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 40 j%101=(balancedTwentyOneTangentSelectedData 40 j : ℤ) := by decide +kernel

private theorem selected_row41 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 41 j%101=(balancedTwentyOneTangentSelectedData 41 j : ℤ) := by decide +kernel

private theorem selected_row42 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 42 j%101=(balancedTwentyOneTangentSelectedData 42 j : ℤ) := by decide +kernel

private theorem selected_row43 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 43 j%101=(balancedTwentyOneTangentSelectedData 43 j : ℤ) := by decide +kernel

private theorem selected_row44 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 44 j%101=(balancedTwentyOneTangentSelectedData 44 j : ℤ) := by decide +kernel

private theorem selected_row45 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 45 j%101=(balancedTwentyOneTangentSelectedData 45 j : ℤ) := by decide +kernel

private theorem selected_row46 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 46 j%101=(balancedTwentyOneTangentSelectedData 46 j : ℤ) := by decide +kernel

private theorem selected_row47 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 47 j%101=(balancedTwentyOneTangentSelectedData 47 j : ℤ) := by decide +kernel

private theorem selected_row48 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 48 j%101=(balancedTwentyOneTangentSelectedData 48 j : ℤ) := by decide +kernel

private theorem selected_row49 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 49 j%101=(balancedTwentyOneTangentSelectedData 49 j : ℤ) := by decide +kernel

private theorem selected_row50 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 50 j%101=(balancedTwentyOneTangentSelectedData 50 j : ℤ) := by decide +kernel

private theorem selected_row51 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 51 j%101=(balancedTwentyOneTangentSelectedData 51 j : ℤ) := by decide +kernel

private theorem selected_row52 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 52 j%101=(balancedTwentyOneTangentSelectedData 52 j : ℤ) := by decide +kernel

private theorem selected_row53 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 53 j%101=(balancedTwentyOneTangentSelectedData 53 j : ℤ) := by decide +kernel

private theorem selected_row54 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 54 j%101=(balancedTwentyOneTangentSelectedData 54 j : ℤ) := by decide +kernel

private theorem selected_row55 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 55 j%101=(balancedTwentyOneTangentSelectedData 55 j : ℤ) := by decide +kernel

private theorem selected_row56 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 56 j%101=(balancedTwentyOneTangentSelectedData 56 j : ℤ) := by decide +kernel

private theorem selected_row57 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 57 j%101=(balancedTwentyOneTangentSelectedData 57 j : ℤ) := by decide +kernel

private theorem selected_row58 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 58 j%101=(balancedTwentyOneTangentSelectedData 58 j : ℤ) := by decide +kernel

private theorem selected_row59 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 59 j%101=(balancedTwentyOneTangentSelectedData 59 j : ℤ) := by decide +kernel

theorem balancedTwentyOneTangent_selected_integer_rows_2 (i j : Fin 60)
    (hlo : 40 ≤ i.val) (hhi : i.val < 60) :
    balancedTwentyOneTangentSelectedIntegerEntry i j%101=(balancedTwentyOneTangentSelectedData i j : ℤ) := by
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
