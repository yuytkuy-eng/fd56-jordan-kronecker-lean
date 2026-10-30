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

private theorem selected_row30 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 30 j%101=(sixOutputThreeColumnFourSeedSelectedData 30 j : ℤ) := by decide +kernel

private theorem selected_row31 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 31 j%101=(sixOutputThreeColumnFourSeedSelectedData 31 j : ℤ) := by decide +kernel

private theorem selected_row32 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 32 j%101=(sixOutputThreeColumnFourSeedSelectedData 32 j : ℤ) := by decide +kernel

private theorem selected_row33 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 33 j%101=(sixOutputThreeColumnFourSeedSelectedData 33 j : ℤ) := by decide +kernel

private theorem selected_row34 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 34 j%101=(sixOutputThreeColumnFourSeedSelectedData 34 j : ℤ) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnFourSeedSelectedIntegerEntry sixOutputThreeColumnFourSeedSelectedData

theorem sixOutputThreeColumnFourSeed_selected_integer_rows_6 (i j : Fin 80)
    (hlo : 30 ≤ i.val) (hhi : i.val < 35) :
    sixOutputThreeColumnFourSeedSelectedIntegerEntry i j%101=(sixOutputThreeColumnFourSeedSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row30 j
  · exact selected_row31 j
  · exact selected_row32 j
  · exact selected_row33 j
  · exact selected_row34 j

end FD56
