/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputTenSeedCriticalBindingBase

/-! A bounded block of exact selected coefficient identities. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

private theorem selected_row30 : ∀ j : Fin 54,
    sixOutputTenSeedCriticalSelectedIntegerEntry 30 j%101=(sixOutputTenSeedCriticalSelectedData 30 j : ℤ) := by decide +kernel

private theorem selected_row31 : ∀ j : Fin 54,
    sixOutputTenSeedCriticalSelectedIntegerEntry 31 j%101=(sixOutputTenSeedCriticalSelectedData 31 j : ℤ) := by decide +kernel

private theorem selected_row32 : ∀ j : Fin 54,
    sixOutputTenSeedCriticalSelectedIntegerEntry 32 j%101=(sixOutputTenSeedCriticalSelectedData 32 j : ℤ) := by decide +kernel

private theorem selected_row33 : ∀ j : Fin 54,
    sixOutputTenSeedCriticalSelectedIntegerEntry 33 j%101=(sixOutputTenSeedCriticalSelectedData 33 j : ℤ) := by decide +kernel

private theorem selected_row34 : ∀ j : Fin 54,
    sixOutputTenSeedCriticalSelectedIntegerEntry 34 j%101=(sixOutputTenSeedCriticalSelectedData 34 j : ℤ) := by decide +kernel

private theorem selected_row35 : ∀ j : Fin 54,
    sixOutputTenSeedCriticalSelectedIntegerEntry 35 j%101=(sixOutputTenSeedCriticalSelectedData 35 j : ℤ) := by decide +kernel

private theorem selected_row36 : ∀ j : Fin 54,
    sixOutputTenSeedCriticalSelectedIntegerEntry 36 j%101=(sixOutputTenSeedCriticalSelectedData 36 j : ℤ) := by decide +kernel

private theorem selected_row37 : ∀ j : Fin 54,
    sixOutputTenSeedCriticalSelectedIntegerEntry 37 j%101=(sixOutputTenSeedCriticalSelectedData 37 j : ℤ) := by decide +kernel

private theorem selected_row38 : ∀ j : Fin 54,
    sixOutputTenSeedCriticalSelectedIntegerEntry 38 j%101=(sixOutputTenSeedCriticalSelectedData 38 j : ℤ) := by decide +kernel

private theorem selected_row39 : ∀ j : Fin 54,
    sixOutputTenSeedCriticalSelectedIntegerEntry 39 j%101=(sixOutputTenSeedCriticalSelectedData 39 j : ℤ) := by decide +kernel

attribute [local irreducible] sixOutputTenSeedCriticalSelectedIntegerEntry sixOutputTenSeedCriticalSelectedData

theorem sixOutputTenSeedCritical_selected_integer_rows_3 (i j : Fin 54)
    (hlo : 30 ≤ i.val) (hhi : i.val < 40) :
    sixOutputTenSeedCriticalSelectedIntegerEntry i j%101=(sixOutputTenSeedCriticalSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
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
