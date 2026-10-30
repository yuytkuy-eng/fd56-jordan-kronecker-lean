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

private theorem selected_row80 : ∀ j : Fin 98,
    sixOutputThreeColumnFourSeedCriticalSelectedIntegerEntry 80 j%101=(sixOutputThreeColumnFourSeedCriticalSelectedData 80 j : ℤ) := by decide +kernel

private theorem selected_row81 : ∀ j : Fin 98,
    sixOutputThreeColumnFourSeedCriticalSelectedIntegerEntry 81 j%101=(sixOutputThreeColumnFourSeedCriticalSelectedData 81 j : ℤ) := by decide +kernel

private theorem selected_row82 : ∀ j : Fin 98,
    sixOutputThreeColumnFourSeedCriticalSelectedIntegerEntry 82 j%101=(sixOutputThreeColumnFourSeedCriticalSelectedData 82 j : ℤ) := by decide +kernel

private theorem selected_row83 : ∀ j : Fin 98,
    sixOutputThreeColumnFourSeedCriticalSelectedIntegerEntry 83 j%101=(sixOutputThreeColumnFourSeedCriticalSelectedData 83 j : ℤ) := by decide +kernel

private theorem selected_row84 : ∀ j : Fin 98,
    sixOutputThreeColumnFourSeedCriticalSelectedIntegerEntry 84 j%101=(sixOutputThreeColumnFourSeedCriticalSelectedData 84 j : ℤ) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnFourSeedCriticalSelectedIntegerEntry sixOutputThreeColumnFourSeedCriticalSelectedData

theorem sixOutputThreeColumnFourSeedCritical_selected_integer_rows_16 (i j : Fin 98)
    (hlo : 80 ≤ i.val) (hhi : i.val < 85) :
    sixOutputThreeColumnFourSeedCriticalSelectedIntegerEntry i j%101=(sixOutputThreeColumnFourSeedCriticalSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row80 j
  · exact selected_row81 j
  · exact selected_row82 j
  · exact selected_row83 j
  · exact selected_row84 j

end FD56
