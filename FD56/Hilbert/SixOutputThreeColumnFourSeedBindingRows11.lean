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

private theorem selected_row55 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 55 j%101=(sixOutputThreeColumnFourSeedSelectedData 55 j : ℤ) := by decide +kernel

private theorem selected_row56 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 56 j%101=(sixOutputThreeColumnFourSeedSelectedData 56 j : ℤ) := by decide +kernel

private theorem selected_row57 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 57 j%101=(sixOutputThreeColumnFourSeedSelectedData 57 j : ℤ) := by decide +kernel

private theorem selected_row58 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 58 j%101=(sixOutputThreeColumnFourSeedSelectedData 58 j : ℤ) := by decide +kernel

private theorem selected_row59 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 59 j%101=(sixOutputThreeColumnFourSeedSelectedData 59 j : ℤ) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnFourSeedSelectedIntegerEntry sixOutputThreeColumnFourSeedSelectedData

theorem sixOutputThreeColumnFourSeed_selected_integer_rows_11 (i j : Fin 80)
    (hlo : 55 ≤ i.val) (hhi : i.val < 60) :
    sixOutputThreeColumnFourSeedSelectedIntegerEntry i j%101=(sixOutputThreeColumnFourSeedSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row55 j
  · exact selected_row56 j
  · exact selected_row57 j
  · exact selected_row58 j
  · exact selected_row59 j

end FD56
