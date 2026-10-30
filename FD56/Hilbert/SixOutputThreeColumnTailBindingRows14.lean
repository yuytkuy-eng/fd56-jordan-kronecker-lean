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

private theorem selected_row70 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 70 j%101=(sixOutputThreeColumnTailSelectedData 70 j : ℤ) := by decide +kernel

private theorem selected_row71 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 71 j%101=(sixOutputThreeColumnTailSelectedData 71 j : ℤ) := by decide +kernel

private theorem selected_row72 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 72 j%101=(sixOutputThreeColumnTailSelectedData 72 j : ℤ) := by decide +kernel

private theorem selected_row73 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 73 j%101=(sixOutputThreeColumnTailSelectedData 73 j : ℤ) := by decide +kernel

private theorem selected_row74 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 74 j%101=(sixOutputThreeColumnTailSelectedData 74 j : ℤ) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnTailSelectedIntegerEntry sixOutputThreeColumnTailSelectedData

theorem sixOutputThreeColumnTail_selected_integer_rows_14 (i j : Fin 120)
    (hlo : 70 ≤ i.val) (hhi : i.val < 75) :
    sixOutputThreeColumnTailSelectedIntegerEntry i j%101=(sixOutputThreeColumnTailSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row70 j
  · exact selected_row71 j
  · exact selected_row72 j
  · exact selected_row73 j
  · exact selected_row74 j

end FD56
