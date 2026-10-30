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

private theorem selected_row85 : ∀ j : Fin 98,
    sixOutputThreeColumnFourSeedCriticalSelectedIntegerEntry 85 j%101=(sixOutputThreeColumnFourSeedCriticalSelectedData 85 j : ℤ) := by decide +kernel

private theorem selected_row86 : ∀ j : Fin 98,
    sixOutputThreeColumnFourSeedCriticalSelectedIntegerEntry 86 j%101=(sixOutputThreeColumnFourSeedCriticalSelectedData 86 j : ℤ) := by decide +kernel

private theorem selected_row87 : ∀ j : Fin 98,
    sixOutputThreeColumnFourSeedCriticalSelectedIntegerEntry 87 j%101=(sixOutputThreeColumnFourSeedCriticalSelectedData 87 j : ℤ) := by decide +kernel

private theorem selected_row88 : ∀ j : Fin 98,
    sixOutputThreeColumnFourSeedCriticalSelectedIntegerEntry 88 j%101=(sixOutputThreeColumnFourSeedCriticalSelectedData 88 j : ℤ) := by decide +kernel

private theorem selected_row89 : ∀ j : Fin 98,
    sixOutputThreeColumnFourSeedCriticalSelectedIntegerEntry 89 j%101=(sixOutputThreeColumnFourSeedCriticalSelectedData 89 j : ℤ) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnFourSeedCriticalSelectedIntegerEntry sixOutputThreeColumnFourSeedCriticalSelectedData

theorem sixOutputThreeColumnFourSeedCritical_selected_integer_rows_17 (i j : Fin 98)
    (hlo : 85 ≤ i.val) (hhi : i.val < 90) :
    sixOutputThreeColumnFourSeedCriticalSelectedIntegerEntry i j%101=(sixOutputThreeColumnFourSeedCriticalSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row85 j
  · exact selected_row86 j
  · exact selected_row87 j
  · exact selected_row88 j
  · exact selected_row89 j

end FD56
