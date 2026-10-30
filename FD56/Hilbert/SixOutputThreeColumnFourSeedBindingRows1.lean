/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputThreeColumnFourSeedBindingBase

/-! Exact integer rows of the selected coefficient certificate. -/

namespace FD56
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000

private theorem selected_row5 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 5 j%101=(sixOutputThreeColumnFourSeedSelectedData 5 j : ℤ) := by decide +kernel

private theorem selected_row6 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 6 j%101=(sixOutputThreeColumnFourSeedSelectedData 6 j : ℤ) := by decide +kernel

private theorem selected_row7 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 7 j%101=(sixOutputThreeColumnFourSeedSelectedData 7 j : ℤ) := by decide +kernel

private theorem selected_row8 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 8 j%101=(sixOutputThreeColumnFourSeedSelectedData 8 j : ℤ) := by decide +kernel

private theorem selected_row9 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 9 j%101=(sixOutputThreeColumnFourSeedSelectedData 9 j : ℤ) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnFourSeedSelectedIntegerEntry sixOutputThreeColumnFourSeedSelectedData

theorem sixOutputThreeColumnFourSeed_selected_integer_rows_1 (i j : Fin 80)
    (hlo : 5 ≤ i.val) (hhi : i.val < 10) :
    sixOutputThreeColumnFourSeedSelectedIntegerEntry i j%101=(sixOutputThreeColumnFourSeedSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row5 j
  · exact selected_row6 j
  · exact selected_row7 j
  · exact selected_row8 j
  · exact selected_row9 j

end FD56
