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

private theorem selected_row95 : ∀ j : Fin 98,
    sixOutputThreeColumnFourSeedCriticalSelectedIntegerEntry 95 j%101=(sixOutputThreeColumnFourSeedCriticalSelectedData 95 j : ℤ) := by decide +kernel

private theorem selected_row96 : ∀ j : Fin 98,
    sixOutputThreeColumnFourSeedCriticalSelectedIntegerEntry 96 j%101=(sixOutputThreeColumnFourSeedCriticalSelectedData 96 j : ℤ) := by decide +kernel

private theorem selected_row97 : ∀ j : Fin 98,
    sixOutputThreeColumnFourSeedCriticalSelectedIntegerEntry 97 j%101=(sixOutputThreeColumnFourSeedCriticalSelectedData 97 j : ℤ) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnFourSeedCriticalSelectedIntegerEntry sixOutputThreeColumnFourSeedCriticalSelectedData

theorem sixOutputThreeColumnFourSeedCritical_selected_integer_rows_19 (i j : Fin 98)
    (hlo : 95 ≤ i.val) (hhi : i.val < 98) :
    sixOutputThreeColumnFourSeedCriticalSelectedIntegerEntry i j%101=(sixOutputThreeColumnFourSeedCriticalSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row95 j
  · exact selected_row96 j
  · exact selected_row97 j

end FD56
