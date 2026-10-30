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

private theorem selected_row50 : ∀ j : Fin 54,
    sixOutputTenSeedCriticalSelectedIntegerEntry 50 j%101=(sixOutputTenSeedCriticalSelectedData 50 j : ℤ) := by decide +kernel

private theorem selected_row51 : ∀ j : Fin 54,
    sixOutputTenSeedCriticalSelectedIntegerEntry 51 j%101=(sixOutputTenSeedCriticalSelectedData 51 j : ℤ) := by decide +kernel

private theorem selected_row52 : ∀ j : Fin 54,
    sixOutputTenSeedCriticalSelectedIntegerEntry 52 j%101=(sixOutputTenSeedCriticalSelectedData 52 j : ℤ) := by decide +kernel

private theorem selected_row53 : ∀ j : Fin 54,
    sixOutputTenSeedCriticalSelectedIntegerEntry 53 j%101=(sixOutputTenSeedCriticalSelectedData 53 j : ℤ) := by decide +kernel

attribute [local irreducible] sixOutputTenSeedCriticalSelectedIntegerEntry sixOutputTenSeedCriticalSelectedData

theorem sixOutputTenSeedCritical_selected_integer_rows_5 (i j : Fin 54)
    (hlo : 50 ≤ i.val) (hhi : i.val < 54) :
    sixOutputTenSeedCriticalSelectedIntegerEntry i j%101=(sixOutputTenSeedCriticalSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row50 j
  · exact selected_row51 j
  · exact selected_row52 j
  · exact selected_row53 j

end FD56
