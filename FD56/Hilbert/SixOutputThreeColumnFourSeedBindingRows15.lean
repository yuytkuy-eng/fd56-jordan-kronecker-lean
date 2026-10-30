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

private theorem selected_row75 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 75 j%101=(sixOutputThreeColumnFourSeedSelectedData 75 j : ℤ) := by decide +kernel

private theorem selected_row76 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 76 j%101=(sixOutputThreeColumnFourSeedSelectedData 76 j : ℤ) := by decide +kernel

private theorem selected_row77 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 77 j%101=(sixOutputThreeColumnFourSeedSelectedData 77 j : ℤ) := by decide +kernel

private theorem selected_row78 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 78 j%101=(sixOutputThreeColumnFourSeedSelectedData 78 j : ℤ) := by decide +kernel

private theorem selected_row79 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 79 j%101=(sixOutputThreeColumnFourSeedSelectedData 79 j : ℤ) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnFourSeedSelectedIntegerEntry sixOutputThreeColumnFourSeedSelectedData

theorem sixOutputThreeColumnFourSeed_selected_integer_rows_15 (i j : Fin 80)
    (hlo : 75 ≤ i.val) (hhi : i.val < 80) :
    sixOutputThreeColumnFourSeedSelectedIntegerEntry i j%101=(sixOutputThreeColumnFourSeedSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row75 j
  · exact selected_row76 j
  · exact selected_row77 j
  · exact selected_row78 j
  · exact selected_row79 j

end FD56
