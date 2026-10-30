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

private theorem selected_row0 : ∀ j : Fin 98,
    sixOutputThreeColumnFourSeedCriticalSelectedIntegerEntry 0 j%101=(sixOutputThreeColumnFourSeedCriticalSelectedData 0 j : ℤ) := by decide +kernel

private theorem selected_row1 : ∀ j : Fin 98,
    sixOutputThreeColumnFourSeedCriticalSelectedIntegerEntry 1 j%101=(sixOutputThreeColumnFourSeedCriticalSelectedData 1 j : ℤ) := by decide +kernel

private theorem selected_row2 : ∀ j : Fin 98,
    sixOutputThreeColumnFourSeedCriticalSelectedIntegerEntry 2 j%101=(sixOutputThreeColumnFourSeedCriticalSelectedData 2 j : ℤ) := by decide +kernel

private theorem selected_row3 : ∀ j : Fin 98,
    sixOutputThreeColumnFourSeedCriticalSelectedIntegerEntry 3 j%101=(sixOutputThreeColumnFourSeedCriticalSelectedData 3 j : ℤ) := by decide +kernel

private theorem selected_row4 : ∀ j : Fin 98,
    sixOutputThreeColumnFourSeedCriticalSelectedIntegerEntry 4 j%101=(sixOutputThreeColumnFourSeedCriticalSelectedData 4 j : ℤ) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnFourSeedCriticalSelectedIntegerEntry sixOutputThreeColumnFourSeedCriticalSelectedData

theorem sixOutputThreeColumnFourSeedCritical_selected_integer_rows_0 (i j : Fin 98)
    (hlo : 0 ≤ i.val) (hhi : i.val < 5) :
    sixOutputThreeColumnFourSeedCriticalSelectedIntegerEntry i j%101=(sixOutputThreeColumnFourSeedCriticalSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row0 j
  · exact selected_row1 j
  · exact selected_row2 j
  · exact selected_row3 j
  · exact selected_row4 j

end FD56
