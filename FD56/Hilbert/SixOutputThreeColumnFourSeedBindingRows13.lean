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

private theorem selected_row65 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 65 j%101=(sixOutputThreeColumnFourSeedSelectedData 65 j : ℤ) := by decide +kernel

private theorem selected_row66 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 66 j%101=(sixOutputThreeColumnFourSeedSelectedData 66 j : ℤ) := by decide +kernel

private theorem selected_row67 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 67 j%101=(sixOutputThreeColumnFourSeedSelectedData 67 j : ℤ) := by decide +kernel

private theorem selected_row68 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 68 j%101=(sixOutputThreeColumnFourSeedSelectedData 68 j : ℤ) := by decide +kernel

private theorem selected_row69 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 69 j%101=(sixOutputThreeColumnFourSeedSelectedData 69 j : ℤ) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnFourSeedSelectedIntegerEntry sixOutputThreeColumnFourSeedSelectedData

theorem sixOutputThreeColumnFourSeed_selected_integer_rows_13 (i j : Fin 80)
    (hlo : 65 ≤ i.val) (hhi : i.val < 70) :
    sixOutputThreeColumnFourSeedSelectedIntegerEntry i j%101=(sixOutputThreeColumnFourSeedSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row65 j
  · exact selected_row66 j
  · exact selected_row67 j
  · exact selected_row68 j
  · exact selected_row69 j

end FD56
