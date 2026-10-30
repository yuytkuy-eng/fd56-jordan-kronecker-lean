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

private theorem selected_row45 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 45 j%101=(sixOutputThreeColumnFourSeedSelectedData 45 j : ℤ) := by decide +kernel

private theorem selected_row46 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 46 j%101=(sixOutputThreeColumnFourSeedSelectedData 46 j : ℤ) := by decide +kernel

private theorem selected_row47 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 47 j%101=(sixOutputThreeColumnFourSeedSelectedData 47 j : ℤ) := by decide +kernel

private theorem selected_row48 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 48 j%101=(sixOutputThreeColumnFourSeedSelectedData 48 j : ℤ) := by decide +kernel

private theorem selected_row49 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 49 j%101=(sixOutputThreeColumnFourSeedSelectedData 49 j : ℤ) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnFourSeedSelectedIntegerEntry sixOutputThreeColumnFourSeedSelectedData

theorem sixOutputThreeColumnFourSeed_selected_integer_rows_9 (i j : Fin 80)
    (hlo : 45 ≤ i.val) (hhi : i.val < 50) :
    sixOutputThreeColumnFourSeedSelectedIntegerEntry i j%101=(sixOutputThreeColumnFourSeedSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row45 j
  · exact selected_row46 j
  · exact selected_row47 j
  · exact selected_row48 j
  · exact selected_row49 j

end FD56
