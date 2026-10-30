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

private theorem selected_row35 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 35 j%101=(sixOutputThreeColumnFourSeedSelectedData 35 j : ℤ) := by decide +kernel

private theorem selected_row36 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 36 j%101=(sixOutputThreeColumnFourSeedSelectedData 36 j : ℤ) := by decide +kernel

private theorem selected_row37 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 37 j%101=(sixOutputThreeColumnFourSeedSelectedData 37 j : ℤ) := by decide +kernel

private theorem selected_row38 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 38 j%101=(sixOutputThreeColumnFourSeedSelectedData 38 j : ℤ) := by decide +kernel

private theorem selected_row39 : ∀ j : Fin 80,
    sixOutputThreeColumnFourSeedSelectedIntegerEntry 39 j%101=(sixOutputThreeColumnFourSeedSelectedData 39 j : ℤ) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnFourSeedSelectedIntegerEntry sixOutputThreeColumnFourSeedSelectedData

theorem sixOutputThreeColumnFourSeed_selected_integer_rows_7 (i j : Fin 80)
    (hlo : 35 ≤ i.val) (hhi : i.val < 40) :
    sixOutputThreeColumnFourSeedSelectedIntegerEntry i j%101=(sixOutputThreeColumnFourSeedSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row35 j
  · exact selected_row36 j
  · exact selected_row37 j
  · exact selected_row38 j
  · exact selected_row39 j

end FD56
