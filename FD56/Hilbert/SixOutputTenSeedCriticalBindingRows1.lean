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

private theorem selected_row10 : ∀ j : Fin 54,
    sixOutputTenSeedCriticalSelectedIntegerEntry 10 j%101=(sixOutputTenSeedCriticalSelectedData 10 j : ℤ) := by decide +kernel

private theorem selected_row11 : ∀ j : Fin 54,
    sixOutputTenSeedCriticalSelectedIntegerEntry 11 j%101=(sixOutputTenSeedCriticalSelectedData 11 j : ℤ) := by decide +kernel

private theorem selected_row12 : ∀ j : Fin 54,
    sixOutputTenSeedCriticalSelectedIntegerEntry 12 j%101=(sixOutputTenSeedCriticalSelectedData 12 j : ℤ) := by decide +kernel

private theorem selected_row13 : ∀ j : Fin 54,
    sixOutputTenSeedCriticalSelectedIntegerEntry 13 j%101=(sixOutputTenSeedCriticalSelectedData 13 j : ℤ) := by decide +kernel

private theorem selected_row14 : ∀ j : Fin 54,
    sixOutputTenSeedCriticalSelectedIntegerEntry 14 j%101=(sixOutputTenSeedCriticalSelectedData 14 j : ℤ) := by decide +kernel

private theorem selected_row15 : ∀ j : Fin 54,
    sixOutputTenSeedCriticalSelectedIntegerEntry 15 j%101=(sixOutputTenSeedCriticalSelectedData 15 j : ℤ) := by decide +kernel

private theorem selected_row16 : ∀ j : Fin 54,
    sixOutputTenSeedCriticalSelectedIntegerEntry 16 j%101=(sixOutputTenSeedCriticalSelectedData 16 j : ℤ) := by decide +kernel

private theorem selected_row17 : ∀ j : Fin 54,
    sixOutputTenSeedCriticalSelectedIntegerEntry 17 j%101=(sixOutputTenSeedCriticalSelectedData 17 j : ℤ) := by decide +kernel

private theorem selected_row18 : ∀ j : Fin 54,
    sixOutputTenSeedCriticalSelectedIntegerEntry 18 j%101=(sixOutputTenSeedCriticalSelectedData 18 j : ℤ) := by decide +kernel

private theorem selected_row19 : ∀ j : Fin 54,
    sixOutputTenSeedCriticalSelectedIntegerEntry 19 j%101=(sixOutputTenSeedCriticalSelectedData 19 j : ℤ) := by decide +kernel

attribute [local irreducible] sixOutputTenSeedCriticalSelectedIntegerEntry sixOutputTenSeedCriticalSelectedData

theorem sixOutputTenSeedCritical_selected_integer_rows_1 (i j : Fin 54)
    (hlo : 10 ≤ i.val) (hhi : i.val < 20) :
    sixOutputTenSeedCriticalSelectedIntegerEntry i j%101=(sixOutputTenSeedCriticalSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row10 j
  · exact selected_row11 j
  · exact selected_row12 j
  · exact selected_row13 j
  · exact selected_row14 j
  · exact selected_row15 j
  · exact selected_row16 j
  · exact selected_row17 j
  · exact selected_row18 j
  · exact selected_row19 j

end FD56
