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

private theorem selected_row40 : ∀ j : Fin 54,
    sixOutputTenSeedCriticalSelectedIntegerEntry 40 j%101=(sixOutputTenSeedCriticalSelectedData 40 j : ℤ) := by decide +kernel

private theorem selected_row41 : ∀ j : Fin 54,
    sixOutputTenSeedCriticalSelectedIntegerEntry 41 j%101=(sixOutputTenSeedCriticalSelectedData 41 j : ℤ) := by decide +kernel

private theorem selected_row42 : ∀ j : Fin 54,
    sixOutputTenSeedCriticalSelectedIntegerEntry 42 j%101=(sixOutputTenSeedCriticalSelectedData 42 j : ℤ) := by decide +kernel

private theorem selected_row43 : ∀ j : Fin 54,
    sixOutputTenSeedCriticalSelectedIntegerEntry 43 j%101=(sixOutputTenSeedCriticalSelectedData 43 j : ℤ) := by decide +kernel

private theorem selected_row44 : ∀ j : Fin 54,
    sixOutputTenSeedCriticalSelectedIntegerEntry 44 j%101=(sixOutputTenSeedCriticalSelectedData 44 j : ℤ) := by decide +kernel

private theorem selected_row45 : ∀ j : Fin 54,
    sixOutputTenSeedCriticalSelectedIntegerEntry 45 j%101=(sixOutputTenSeedCriticalSelectedData 45 j : ℤ) := by decide +kernel

private theorem selected_row46 : ∀ j : Fin 54,
    sixOutputTenSeedCriticalSelectedIntegerEntry 46 j%101=(sixOutputTenSeedCriticalSelectedData 46 j : ℤ) := by decide +kernel

private theorem selected_row47 : ∀ j : Fin 54,
    sixOutputTenSeedCriticalSelectedIntegerEntry 47 j%101=(sixOutputTenSeedCriticalSelectedData 47 j : ℤ) := by decide +kernel

private theorem selected_row48 : ∀ j : Fin 54,
    sixOutputTenSeedCriticalSelectedIntegerEntry 48 j%101=(sixOutputTenSeedCriticalSelectedData 48 j : ℤ) := by decide +kernel

private theorem selected_row49 : ∀ j : Fin 54,
    sixOutputTenSeedCriticalSelectedIntegerEntry 49 j%101=(sixOutputTenSeedCriticalSelectedData 49 j : ℤ) := by decide +kernel

attribute [local irreducible] sixOutputTenSeedCriticalSelectedIntegerEntry sixOutputTenSeedCriticalSelectedData

theorem sixOutputTenSeedCritical_selected_integer_rows_4 (i j : Fin 54)
    (hlo : 40 ≤ i.val) (hhi : i.val < 50) :
    sixOutputTenSeedCriticalSelectedIntegerEntry i j%101=(sixOutputTenSeedCriticalSelectedData i j : ℤ) := by
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
