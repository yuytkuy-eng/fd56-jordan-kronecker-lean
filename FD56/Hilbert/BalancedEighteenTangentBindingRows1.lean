/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedEighteenTangentBindingBase

/-! A bounded block of exact selected coefficient identities. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

private theorem selected_row20 : ∀ j : Fin 50,
    balancedEighteenTangentSelectedIntegerEntry 20 j%101=(balancedEighteenTangentSelectedData 20 j : ℤ) := by decide +kernel

private theorem selected_row21 : ∀ j : Fin 50,
    balancedEighteenTangentSelectedIntegerEntry 21 j%101=(balancedEighteenTangentSelectedData 21 j : ℤ) := by decide +kernel

private theorem selected_row22 : ∀ j : Fin 50,
    balancedEighteenTangentSelectedIntegerEntry 22 j%101=(balancedEighteenTangentSelectedData 22 j : ℤ) := by decide +kernel

private theorem selected_row23 : ∀ j : Fin 50,
    balancedEighteenTangentSelectedIntegerEntry 23 j%101=(balancedEighteenTangentSelectedData 23 j : ℤ) := by decide +kernel

private theorem selected_row24 : ∀ j : Fin 50,
    balancedEighteenTangentSelectedIntegerEntry 24 j%101=(balancedEighteenTangentSelectedData 24 j : ℤ) := by decide +kernel

private theorem selected_row25 : ∀ j : Fin 50,
    balancedEighteenTangentSelectedIntegerEntry 25 j%101=(balancedEighteenTangentSelectedData 25 j : ℤ) := by decide +kernel

private theorem selected_row26 : ∀ j : Fin 50,
    balancedEighteenTangentSelectedIntegerEntry 26 j%101=(balancedEighteenTangentSelectedData 26 j : ℤ) := by decide +kernel

private theorem selected_row27 : ∀ j : Fin 50,
    balancedEighteenTangentSelectedIntegerEntry 27 j%101=(balancedEighteenTangentSelectedData 27 j : ℤ) := by decide +kernel

private theorem selected_row28 : ∀ j : Fin 50,
    balancedEighteenTangentSelectedIntegerEntry 28 j%101=(balancedEighteenTangentSelectedData 28 j : ℤ) := by decide +kernel

private theorem selected_row29 : ∀ j : Fin 50,
    balancedEighteenTangentSelectedIntegerEntry 29 j%101=(balancedEighteenTangentSelectedData 29 j : ℤ) := by decide +kernel

private theorem selected_row30 : ∀ j : Fin 50,
    balancedEighteenTangentSelectedIntegerEntry 30 j%101=(balancedEighteenTangentSelectedData 30 j : ℤ) := by decide +kernel

private theorem selected_row31 : ∀ j : Fin 50,
    balancedEighteenTangentSelectedIntegerEntry 31 j%101=(balancedEighteenTangentSelectedData 31 j : ℤ) := by decide +kernel

private theorem selected_row32 : ∀ j : Fin 50,
    balancedEighteenTangentSelectedIntegerEntry 32 j%101=(balancedEighteenTangentSelectedData 32 j : ℤ) := by decide +kernel

private theorem selected_row33 : ∀ j : Fin 50,
    balancedEighteenTangentSelectedIntegerEntry 33 j%101=(balancedEighteenTangentSelectedData 33 j : ℤ) := by decide +kernel

private theorem selected_row34 : ∀ j : Fin 50,
    balancedEighteenTangentSelectedIntegerEntry 34 j%101=(balancedEighteenTangentSelectedData 34 j : ℤ) := by decide +kernel

private theorem selected_row35 : ∀ j : Fin 50,
    balancedEighteenTangentSelectedIntegerEntry 35 j%101=(balancedEighteenTangentSelectedData 35 j : ℤ) := by decide +kernel

private theorem selected_row36 : ∀ j : Fin 50,
    balancedEighteenTangentSelectedIntegerEntry 36 j%101=(balancedEighteenTangentSelectedData 36 j : ℤ) := by decide +kernel

private theorem selected_row37 : ∀ j : Fin 50,
    balancedEighteenTangentSelectedIntegerEntry 37 j%101=(balancedEighteenTangentSelectedData 37 j : ℤ) := by decide +kernel

private theorem selected_row38 : ∀ j : Fin 50,
    balancedEighteenTangentSelectedIntegerEntry 38 j%101=(balancedEighteenTangentSelectedData 38 j : ℤ) := by decide +kernel

private theorem selected_row39 : ∀ j : Fin 50,
    balancedEighteenTangentSelectedIntegerEntry 39 j%101=(balancedEighteenTangentSelectedData 39 j : ℤ) := by decide +kernel

attribute [local irreducible] balancedEighteenTangentSelectedIntegerEntry balancedEighteenTangentSelectedData

theorem balancedEighteenTangent_selected_integer_rows_1 (i j : Fin 50)
    (hlo : 20 ≤ i.val) (hhi : i.val < 40) :
    balancedEighteenTangentSelectedIntegerEntry i j%101=(balancedEighteenTangentSelectedData i j : ℤ) := by
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
