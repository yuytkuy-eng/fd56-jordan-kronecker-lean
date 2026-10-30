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

private theorem selected_row40 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 40 j%101=(sixOutputThreeColumnFourSeedSelectedData 40 j : ℤ) := by decide +kernel

private theorem selected_row41 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 41 j%101=(sixOutputThreeColumnFourSeedSelectedData 41 j : ℤ) := by decide +kernel

private theorem selected_row42 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 42 j%101=(sixOutputThreeColumnFourSeedSelectedData 42 j : ℤ) := by decide +kernel

private theorem selected_row43 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 43 j%101=(sixOutputThreeColumnFourSeedSelectedData 43 j : ℤ) := by decide +kernel

private theorem selected_row44 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 44 j%101=(sixOutputThreeColumnFourSeedSelectedData 44 j : ℤ) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnFourSeedSelectedIntegerEntry sixOutputThreeColumnFourSeedSelectedData

theorem sixOutputThreeColumnFourSeed_selected_integer_rows_8 (i j : Fin 80)
    (hlo : 40 ≤ i.val) (hhi : i.val < 45) :
    sixOutputThreeColumnFourSeedSelectedIntegerEntry i j%101=(sixOutputThreeColumnFourSeedSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row40 j
  · exact selected_row41 j
  · exact selected_row42 j
  · exact selected_row43 j
  · exact selected_row44 j

end FD56
