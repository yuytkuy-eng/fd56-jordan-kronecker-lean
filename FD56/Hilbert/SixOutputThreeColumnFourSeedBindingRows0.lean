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

private theorem selected_row0 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 0 j%101=(sixOutputThreeColumnFourSeedSelectedData 0 j : ℤ) := by decide +kernel

private theorem selected_row1 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 1 j%101=(sixOutputThreeColumnFourSeedSelectedData 1 j : ℤ) := by decide +kernel

private theorem selected_row2 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 2 j%101=(sixOutputThreeColumnFourSeedSelectedData 2 j : ℤ) := by decide +kernel

private theorem selected_row3 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 3 j%101=(sixOutputThreeColumnFourSeedSelectedData 3 j : ℤ) := by decide +kernel

private theorem selected_row4 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 4 j%101=(sixOutputThreeColumnFourSeedSelectedData 4 j : ℤ) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnFourSeedSelectedIntegerEntry sixOutputThreeColumnFourSeedSelectedData

theorem sixOutputThreeColumnFourSeed_selected_integer_rows_0 (i j : Fin 80)
    (hlo : 0 ≤ i.val) (hhi : i.val < 5) :
    sixOutputThreeColumnFourSeedSelectedIntegerEntry i j%101=(sixOutputThreeColumnFourSeedSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row0 j
  · exact selected_row1 j
  · exact selected_row2 j
  · exact selected_row3 j
  · exact selected_row4 j

end FD56
