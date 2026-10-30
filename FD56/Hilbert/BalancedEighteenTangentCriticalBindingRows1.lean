/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedEighteenTangentCriticalBindingBase

/-! A bounded block of exact selected coefficient identities. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

private theorem selected_row20 : ∀ j : Fin 54,
    balancedEighteenTangentCriticalSelectedIntegerEntry 20 j%101=(balancedEighteenTangentCriticalSelectedData 20 j : ℤ) := by decide +kernel

private theorem selected_row21 : ∀ j : Fin 54,
    balancedEighteenTangentCriticalSelectedIntegerEntry 21 j%101=(balancedEighteenTangentCriticalSelectedData 21 j : ℤ) := by decide +kernel

private theorem selected_row22 : ∀ j : Fin 54,
    balancedEighteenTangentCriticalSelectedIntegerEntry 22 j%101=(balancedEighteenTangentCriticalSelectedData 22 j : ℤ) := by decide +kernel

private theorem selected_row23 : ∀ j : Fin 54,
    balancedEighteenTangentCriticalSelectedIntegerEntry 23 j%101=(balancedEighteenTangentCriticalSelectedData 23 j : ℤ) := by decide +kernel

private theorem selected_row24 : ∀ j : Fin 54,
    balancedEighteenTangentCriticalSelectedIntegerEntry 24 j%101=(balancedEighteenTangentCriticalSelectedData 24 j : ℤ) := by decide +kernel

private theorem selected_row25 : ∀ j : Fin 54,
    balancedEighteenTangentCriticalSelectedIntegerEntry 25 j%101=(balancedEighteenTangentCriticalSelectedData 25 j : ℤ) := by decide +kernel

private theorem selected_row26 : ∀ j : Fin 54,
    balancedEighteenTangentCriticalSelectedIntegerEntry 26 j%101=(balancedEighteenTangentCriticalSelectedData 26 j : ℤ) := by decide +kernel

private theorem selected_row27 : ∀ j : Fin 54,
    balancedEighteenTangentCriticalSelectedIntegerEntry 27 j%101=(balancedEighteenTangentCriticalSelectedData 27 j : ℤ) := by decide +kernel

private theorem selected_row28 : ∀ j : Fin 54,
    balancedEighteenTangentCriticalSelectedIntegerEntry 28 j%101=(balancedEighteenTangentCriticalSelectedData 28 j : ℤ) := by decide +kernel

private theorem selected_row29 : ∀ j : Fin 54,
    balancedEighteenTangentCriticalSelectedIntegerEntry 29 j%101=(balancedEighteenTangentCriticalSelectedData 29 j : ℤ) := by decide +kernel

private theorem selected_row30 : ∀ j : Fin 54,
    balancedEighteenTangentCriticalSelectedIntegerEntry 30 j%101=(balancedEighteenTangentCriticalSelectedData 30 j : ℤ) := by decide +kernel

private theorem selected_row31 : ∀ j : Fin 54,
    balancedEighteenTangentCriticalSelectedIntegerEntry 31 j%101=(balancedEighteenTangentCriticalSelectedData 31 j : ℤ) := by decide +kernel

private theorem selected_row32 : ∀ j : Fin 54,
    balancedEighteenTangentCriticalSelectedIntegerEntry 32 j%101=(balancedEighteenTangentCriticalSelectedData 32 j : ℤ) := by decide +kernel

private theorem selected_row33 : ∀ j : Fin 54,
    balancedEighteenTangentCriticalSelectedIntegerEntry 33 j%101=(balancedEighteenTangentCriticalSelectedData 33 j : ℤ) := by decide +kernel

private theorem selected_row34 : ∀ j : Fin 54,
    balancedEighteenTangentCriticalSelectedIntegerEntry 34 j%101=(balancedEighteenTangentCriticalSelectedData 34 j : ℤ) := by decide +kernel

private theorem selected_row35 : ∀ j : Fin 54,
    balancedEighteenTangentCriticalSelectedIntegerEntry 35 j%101=(balancedEighteenTangentCriticalSelectedData 35 j : ℤ) := by decide +kernel

private theorem selected_row36 : ∀ j : Fin 54,
    balancedEighteenTangentCriticalSelectedIntegerEntry 36 j%101=(balancedEighteenTangentCriticalSelectedData 36 j : ℤ) := by decide +kernel

private theorem selected_row37 : ∀ j : Fin 54,
    balancedEighteenTangentCriticalSelectedIntegerEntry 37 j%101=(balancedEighteenTangentCriticalSelectedData 37 j : ℤ) := by decide +kernel

private theorem selected_row38 : ∀ j : Fin 54,
    balancedEighteenTangentCriticalSelectedIntegerEntry 38 j%101=(balancedEighteenTangentCriticalSelectedData 38 j : ℤ) := by decide +kernel

private theorem selected_row39 : ∀ j : Fin 54,
    balancedEighteenTangentCriticalSelectedIntegerEntry 39 j%101=(balancedEighteenTangentCriticalSelectedData 39 j : ℤ) := by decide +kernel

attribute [local irreducible] balancedEighteenTangentCriticalSelectedIntegerEntry balancedEighteenTangentCriticalSelectedData

theorem balancedEighteenTangentCritical_selected_integer_rows_1 (i j : Fin 54)
    (hlo : 20 ≤ i.val) (hhi : i.val < 40) :
    balancedEighteenTangentCriticalSelectedIntegerEntry i j%101=(balancedEighteenTangentCriticalSelectedData i j : ℤ) := by
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
