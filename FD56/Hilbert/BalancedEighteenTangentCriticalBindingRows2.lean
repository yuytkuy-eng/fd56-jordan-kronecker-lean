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

private theorem selected_row40 : ∀ j : Fin 54,
    balancedEighteenTangentCriticalSelectedIntegerEntry 40 j%101=(balancedEighteenTangentCriticalSelectedData 40 j : ℤ) := by decide +kernel

private theorem selected_row41 : ∀ j : Fin 54,
    balancedEighteenTangentCriticalSelectedIntegerEntry 41 j%101=(balancedEighteenTangentCriticalSelectedData 41 j : ℤ) := by decide +kernel

private theorem selected_row42 : ∀ j : Fin 54,
    balancedEighteenTangentCriticalSelectedIntegerEntry 42 j%101=(balancedEighteenTangentCriticalSelectedData 42 j : ℤ) := by decide +kernel

private theorem selected_row43 : ∀ j : Fin 54,
    balancedEighteenTangentCriticalSelectedIntegerEntry 43 j%101=(balancedEighteenTangentCriticalSelectedData 43 j : ℤ) := by decide +kernel

private theorem selected_row44 : ∀ j : Fin 54,
    balancedEighteenTangentCriticalSelectedIntegerEntry 44 j%101=(balancedEighteenTangentCriticalSelectedData 44 j : ℤ) := by decide +kernel

private theorem selected_row45 : ∀ j : Fin 54,
    balancedEighteenTangentCriticalSelectedIntegerEntry 45 j%101=(balancedEighteenTangentCriticalSelectedData 45 j : ℤ) := by decide +kernel

private theorem selected_row46 : ∀ j : Fin 54,
    balancedEighteenTangentCriticalSelectedIntegerEntry 46 j%101=(balancedEighteenTangentCriticalSelectedData 46 j : ℤ) := by decide +kernel

private theorem selected_row47 : ∀ j : Fin 54,
    balancedEighteenTangentCriticalSelectedIntegerEntry 47 j%101=(balancedEighteenTangentCriticalSelectedData 47 j : ℤ) := by decide +kernel

private theorem selected_row48 : ∀ j : Fin 54,
    balancedEighteenTangentCriticalSelectedIntegerEntry 48 j%101=(balancedEighteenTangentCriticalSelectedData 48 j : ℤ) := by decide +kernel

private theorem selected_row49 : ∀ j : Fin 54,
    balancedEighteenTangentCriticalSelectedIntegerEntry 49 j%101=(balancedEighteenTangentCriticalSelectedData 49 j : ℤ) := by decide +kernel

private theorem selected_row50 : ∀ j : Fin 54,
    balancedEighteenTangentCriticalSelectedIntegerEntry 50 j%101=(balancedEighteenTangentCriticalSelectedData 50 j : ℤ) := by decide +kernel

private theorem selected_row51 : ∀ j : Fin 54,
    balancedEighteenTangentCriticalSelectedIntegerEntry 51 j%101=(balancedEighteenTangentCriticalSelectedData 51 j : ℤ) := by decide +kernel

private theorem selected_row52 : ∀ j : Fin 54,
    balancedEighteenTangentCriticalSelectedIntegerEntry 52 j%101=(balancedEighteenTangentCriticalSelectedData 52 j : ℤ) := by decide +kernel

private theorem selected_row53 : ∀ j : Fin 54,
    balancedEighteenTangentCriticalSelectedIntegerEntry 53 j%101=(balancedEighteenTangentCriticalSelectedData 53 j : ℤ) := by decide +kernel

attribute [local irreducible] balancedEighteenTangentCriticalSelectedIntegerEntry balancedEighteenTangentCriticalSelectedData

theorem balancedEighteenTangentCritical_selected_integer_rows_2 (i j : Fin 54)
    (hlo : 40 ≤ i.val) (hhi : i.val < 54) :
    balancedEighteenTangentCriticalSelectedIntegerEntry i j%101=(balancedEighteenTangentCriticalSelectedData i j : ℤ) := by
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

end FD56
