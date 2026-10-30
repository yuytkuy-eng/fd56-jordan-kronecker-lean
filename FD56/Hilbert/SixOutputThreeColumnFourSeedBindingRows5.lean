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

private theorem selected_row25 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 25 j%101=(sixOutputThreeColumnFourSeedSelectedData 25 j : ℤ) := by decide +kernel

private theorem selected_row26 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 26 j%101=(sixOutputThreeColumnFourSeedSelectedData 26 j : ℤ) := by decide +kernel

private theorem selected_row27 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 27 j%101=(sixOutputThreeColumnFourSeedSelectedData 27 j : ℤ) := by decide +kernel

private theorem selected_row28 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 28 j%101=(sixOutputThreeColumnFourSeedSelectedData 28 j : ℤ) := by decide +kernel

private theorem selected_row29 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 29 j%101=(sixOutputThreeColumnFourSeedSelectedData 29 j : ℤ) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnFourSeedSelectedIntegerEntry sixOutputThreeColumnFourSeedSelectedData

theorem sixOutputThreeColumnFourSeed_selected_integer_rows_5 (i j : Fin 80)
    (hlo : 25 ≤ i.val) (hhi : i.val < 30) :
    sixOutputThreeColumnFourSeedSelectedIntegerEntry i j%101=(sixOutputThreeColumnFourSeedSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row25 j
  · exact selected_row26 j
  · exact selected_row27 j
  · exact selected_row28 j
  · exact selected_row29 j

end FD56
