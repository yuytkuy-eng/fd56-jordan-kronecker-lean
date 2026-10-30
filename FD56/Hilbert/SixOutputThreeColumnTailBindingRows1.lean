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

private theorem selected_row5 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 5 j%101=(sixOutputThreeColumnTailSelectedData 5 j : ℤ) := by decide +kernel

private theorem selected_row6 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 6 j%101=(sixOutputThreeColumnTailSelectedData 6 j : ℤ) := by decide +kernel

private theorem selected_row7 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 7 j%101=(sixOutputThreeColumnTailSelectedData 7 j : ℤ) := by decide +kernel

private theorem selected_row8 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 8 j%101=(sixOutputThreeColumnTailSelectedData 8 j : ℤ) := by decide +kernel

private theorem selected_row9 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 9 j%101=(sixOutputThreeColumnTailSelectedData 9 j : ℤ) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnTailSelectedIntegerEntry sixOutputThreeColumnTailSelectedData

theorem sixOutputThreeColumnTail_selected_integer_rows_1 (i j : Fin 120)
    (hlo : 5 ≤ i.val) (hhi : i.val < 10) :
    sixOutputThreeColumnTailSelectedIntegerEntry i j%101=(sixOutputThreeColumnTailSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row5 j
  · exact selected_row6 j
  · exact selected_row7 j
  · exact selected_row8 j
  · exact selected_row9 j

end FD56
