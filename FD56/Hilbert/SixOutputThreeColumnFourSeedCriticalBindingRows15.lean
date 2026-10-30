/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputThreeColumnFourSeedCriticalBindingBase

/-! Exact integer rows of the selected coefficient certificate. -/

namespace FD56
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000

private theorem selected_row75 : ∀ j : Fin 98,
    sixOutputThreeColumnFourSeedCriticalSelectedIntegerEntry 75 j%101=(sixOutputThreeColumnFourSeedCriticalSelectedData 75 j : ℤ) := by decide +kernel

private theorem selected_row76 : ∀ j : Fin 98,
    sixOutputThreeColumnFourSeedCriticalSelectedIntegerEntry 76 j%101=(sixOutputThreeColumnFourSeedCriticalSelectedData 76 j : ℤ) := by decide +kernel

private theorem selected_row77 : ∀ j : Fin 98,
    sixOutputThreeColumnFourSeedCriticalSelectedIntegerEntry 77 j%101=(sixOutputThreeColumnFourSeedCriticalSelectedData 77 j : ℤ) := by decide +kernel

private theorem selected_row78 : ∀ j : Fin 98,
    sixOutputThreeColumnFourSeedCriticalSelectedIntegerEntry 78 j%101=(sixOutputThreeColumnFourSeedCriticalSelectedData 78 j : ℤ) := by decide +kernel

private theorem selected_row79 : ∀ j : Fin 98,
    sixOutputThreeColumnFourSeedCriticalSelectedIntegerEntry 79 j%101=(sixOutputThreeColumnFourSeedCriticalSelectedData 79 j : ℤ) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnFourSeedCriticalSelectedIntegerEntry sixOutputThreeColumnFourSeedCriticalSelectedData

theorem sixOutputThreeColumnFourSeedCritical_selected_integer_rows_15 (i j : Fin 98)
    (hlo : 75 ≤ i.val) (hhi : i.val < 80) :
    sixOutputThreeColumnFourSeedCriticalSelectedIntegerEntry i j%101=(sixOutputThreeColumnFourSeedCriticalSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row75 j
  · exact selected_row76 j
  · exact selected_row77 j
  · exact selected_row78 j
  · exact selected_row79 j

end FD56
