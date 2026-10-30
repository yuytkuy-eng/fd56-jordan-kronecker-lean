/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputThreeColumnTailBindingBase

/-! Five exact rows of the selected degree-five coefficient certificate. -/

namespace FD56
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000

private theorem selected_row0 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 0 j%101=(sixOutputThreeColumnTailSelectedData 0 j : ℤ) := by decide +kernel

private theorem selected_row1 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 1 j%101=(sixOutputThreeColumnTailSelectedData 1 j : ℤ) := by decide +kernel

private theorem selected_row2 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 2 j%101=(sixOutputThreeColumnTailSelectedData 2 j : ℤ) := by decide +kernel

private theorem selected_row3 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 3 j%101=(sixOutputThreeColumnTailSelectedData 3 j : ℤ) := by decide +kernel

private theorem selected_row4 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 4 j%101=(sixOutputThreeColumnTailSelectedData 4 j : ℤ) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnTailSelectedIntegerEntry sixOutputThreeColumnTailSelectedData

theorem sixOutputThreeColumnTail_selected_integer_rows_0 (i j : Fin 120)
    (hlo : 0 ≤ i.val) (hhi : i.val < 5) :
    sixOutputThreeColumnTailSelectedIntegerEntry i j%101=(sixOutputThreeColumnTailSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row0 j
  · exact selected_row1 j
  · exact selected_row2 j
  · exact selected_row3 j
  · exact selected_row4 j

end FD56
