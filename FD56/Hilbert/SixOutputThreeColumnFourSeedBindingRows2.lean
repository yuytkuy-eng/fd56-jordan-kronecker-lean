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

private theorem selected_row10 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 10 j%101=(sixOutputThreeColumnFourSeedSelectedData 10 j : ℤ) := by decide +kernel

private theorem selected_row11 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 11 j%101=(sixOutputThreeColumnFourSeedSelectedData 11 j : ℤ) := by decide +kernel

private theorem selected_row12 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 12 j%101=(sixOutputThreeColumnFourSeedSelectedData 12 j : ℤ) := by decide +kernel

private theorem selected_row13 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 13 j%101=(sixOutputThreeColumnFourSeedSelectedData 13 j : ℤ) := by decide +kernel

private theorem selected_row14 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 14 j%101=(sixOutputThreeColumnFourSeedSelectedData 14 j : ℤ) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnFourSeedSelectedIntegerEntry sixOutputThreeColumnFourSeedSelectedData

theorem sixOutputThreeColumnFourSeed_selected_integer_rows_2 (i j : Fin 80)
    (hlo : 10 ≤ i.val) (hhi : i.val < 15) :
    sixOutputThreeColumnFourSeedSelectedIntegerEntry i j%101=(sixOutputThreeColumnFourSeedSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row10 j
  · exact selected_row11 j
  · exact selected_row12 j
  · exact selected_row13 j
  · exact selected_row14 j

end FD56
