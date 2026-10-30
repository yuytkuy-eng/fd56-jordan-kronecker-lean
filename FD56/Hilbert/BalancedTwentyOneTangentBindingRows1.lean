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

private theorem selected_row20 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 20 j%101=(balancedTwentyOneTangentSelectedData 20 j : ℤ) := by decide +kernel

private theorem selected_row21 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 21 j%101=(balancedTwentyOneTangentSelectedData 21 j : ℤ) := by decide +kernel

private theorem selected_row22 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 22 j%101=(balancedTwentyOneTangentSelectedData 22 j : ℤ) := by decide +kernel

private theorem selected_row23 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 23 j%101=(balancedTwentyOneTangentSelectedData 23 j : ℤ) := by decide +kernel

private theorem selected_row24 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 24 j%101=(balancedTwentyOneTangentSelectedData 24 j : ℤ) := by decide +kernel

private theorem selected_row25 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 25 j%101=(balancedTwentyOneTangentSelectedData 25 j : ℤ) := by decide +kernel

private theorem selected_row26 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 26 j%101=(balancedTwentyOneTangentSelectedData 26 j : ℤ) := by decide +kernel

private theorem selected_row27 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 27 j%101=(balancedTwentyOneTangentSelectedData 27 j : ℤ) := by decide +kernel

private theorem selected_row28 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 28 j%101=(balancedTwentyOneTangentSelectedData 28 j : ℤ) := by decide +kernel

private theorem selected_row29 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 29 j%101=(balancedTwentyOneTangentSelectedData 29 j : ℤ) := by decide +kernel

private theorem selected_row30 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 30 j%101=(balancedTwentyOneTangentSelectedData 30 j : ℤ) := by decide +kernel

private theorem selected_row31 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 31 j%101=(balancedTwentyOneTangentSelectedData 31 j : ℤ) := by decide +kernel

private theorem selected_row32 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 32 j%101=(balancedTwentyOneTangentSelectedData 32 j : ℤ) := by decide +kernel

private theorem selected_row33 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 33 j%101=(balancedTwentyOneTangentSelectedData 33 j : ℤ) := by decide +kernel

private theorem selected_row34 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 34 j%101=(balancedTwentyOneTangentSelectedData 34 j : ℤ) := by decide +kernel

private theorem selected_row35 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 35 j%101=(balancedTwentyOneTangentSelectedData 35 j : ℤ) := by decide +kernel

private theorem selected_row36 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 36 j%101=(balancedTwentyOneTangentSelectedData 36 j : ℤ) := by decide +kernel

private theorem selected_row37 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 37 j%101=(balancedTwentyOneTangentSelectedData 37 j : ℤ) := by decide +kernel

private theorem selected_row38 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 38 j%101=(balancedTwentyOneTangentSelectedData 38 j : ℤ) := by decide +kernel

private theorem selected_row39 : ∀ j : Fin 60,
    balancedTwentyOneTangentSelectedIntegerEntry 39 j%101=(balancedTwentyOneTangentSelectedData 39 j : ℤ) := by decide +kernel

theorem balancedTwentyOneTangent_selected_integer_rows_1 (i j : Fin 60)
    (hlo : 20 ≤ i.val) (hhi : i.val < 40) :
    balancedTwentyOneTangentSelectedIntegerEntry i j%101=(balancedTwentyOneTangentSelectedData i j : ℤ) := by
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
  · exact selected_row30 j
  · exact selected_row31 j
  · exact selected_row32 j
  · exact selected_row33 j
  · exact selected_row34 j
  · exact selected_row35 j
  · exact selected_row36 j
  · exact selected_row37 j
  · exact selected_row38 j
  · exact selected_row39 j

end FD56
