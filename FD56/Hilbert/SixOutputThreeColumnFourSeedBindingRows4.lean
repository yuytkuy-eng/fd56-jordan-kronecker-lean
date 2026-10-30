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

private theorem selected_row20 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 20 j%101=(sixOutputThreeColumnFourSeedSelectedData 20 j : ℤ) := by decide +kernel

private theorem selected_row21 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 21 j%101=(sixOutputThreeColumnFourSeedSelectedData 21 j : ℤ) := by decide +kernel

private theorem selected_row22 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 22 j%101=(sixOutputThreeColumnFourSeedSelectedData 22 j : ℤ) := by decide +kernel

private theorem selected_row23 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 23 j%101=(sixOutputThreeColumnFourSeedSelectedData 23 j : ℤ) := by decide +kernel

private theorem selected_row24 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 24 j%101=(sixOutputThreeColumnFourSeedSelectedData 24 j : ℤ) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnFourSeedSelectedIntegerEntry sixOutputThreeColumnFourSeedSelectedData

theorem sixOutputThreeColumnFourSeed_selected_integer_rows_4 (i j : Fin 80)
    (hlo : 20 ≤ i.val) (hhi : i.val < 25) :
    sixOutputThreeColumnFourSeedSelectedIntegerEntry i j%101=(sixOutputThreeColumnFourSeedSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row20 j
  · exact selected_row21 j
  · exact selected_row22 j
  · exact selected_row23 j
  · exact selected_row24 j

end FD56
