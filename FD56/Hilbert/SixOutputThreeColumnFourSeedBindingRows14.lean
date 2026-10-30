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

private theorem selected_row70 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 70 j%101=(sixOutputThreeColumnFourSeedSelectedData 70 j : ℤ) := by decide +kernel

private theorem selected_row71 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 71 j%101=(sixOutputThreeColumnFourSeedSelectedData 71 j : ℤ) := by decide +kernel

private theorem selected_row72 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 72 j%101=(sixOutputThreeColumnFourSeedSelectedData 72 j : ℤ) := by decide +kernel

private theorem selected_row73 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 73 j%101=(sixOutputThreeColumnFourSeedSelectedData 73 j : ℤ) := by decide +kernel

private theorem selected_row74 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 74 j%101=(sixOutputThreeColumnFourSeedSelectedData 74 j : ℤ) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnFourSeedSelectedIntegerEntry sixOutputThreeColumnFourSeedSelectedData

theorem sixOutputThreeColumnFourSeed_selected_integer_rows_14 (i j : Fin 80)
    (hlo : 70 ≤ i.val) (hhi : i.val < 75) :
    sixOutputThreeColumnFourSeedSelectedIntegerEntry i j%101=(sixOutputThreeColumnFourSeedSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row70 j
  · exact selected_row71 j
  · exact selected_row72 j
  · exact selected_row73 j
  · exact selected_row74 j

end FD56
