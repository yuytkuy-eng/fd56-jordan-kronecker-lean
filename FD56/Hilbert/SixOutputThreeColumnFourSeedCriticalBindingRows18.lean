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

private theorem selected_row90 : ∀ j : Fin 98,
    sixOutputThreeColumnFourSeedCriticalSelectedIntegerEntry 90 j%101=(sixOutputThreeColumnFourSeedCriticalSelectedData 90 j : ℤ) := by decide +kernel

private theorem selected_row91 : ∀ j : Fin 98,
    sixOutputThreeColumnFourSeedCriticalSelectedIntegerEntry 91 j%101=(sixOutputThreeColumnFourSeedCriticalSelectedData 91 j : ℤ) := by decide +kernel

private theorem selected_row92 : ∀ j : Fin 98,
    sixOutputThreeColumnFourSeedCriticalSelectedIntegerEntry 92 j%101=(sixOutputThreeColumnFourSeedCriticalSelectedData 92 j : ℤ) := by decide +kernel

private theorem selected_row93 : ∀ j : Fin 98,
    sixOutputThreeColumnFourSeedCriticalSelectedIntegerEntry 93 j%101=(sixOutputThreeColumnFourSeedCriticalSelectedData 93 j : ℤ) := by decide +kernel

private theorem selected_row94 : ∀ j : Fin 98,
    sixOutputThreeColumnFourSeedCriticalSelectedIntegerEntry 94 j%101=(sixOutputThreeColumnFourSeedCriticalSelectedData 94 j : ℤ) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnFourSeedCriticalSelectedIntegerEntry sixOutputThreeColumnFourSeedCriticalSelectedData

theorem sixOutputThreeColumnFourSeedCritical_selected_integer_rows_18 (i j : Fin 98)
    (hlo : 90 ≤ i.val) (hhi : i.val < 95) :
    sixOutputThreeColumnFourSeedCriticalSelectedIntegerEntry i j%101=(sixOutputThreeColumnFourSeedCriticalSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row90 j
  · exact selected_row91 j
  · exact selected_row92 j
  · exact selected_row93 j
  · exact selected_row94 j

end FD56
