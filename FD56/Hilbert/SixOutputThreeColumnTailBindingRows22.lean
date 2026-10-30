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

private theorem selected_row110 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 110 j%101=(sixOutputThreeColumnTailSelectedData 110 j : ℤ) := by decide +kernel

private theorem selected_row111 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 111 j%101=(sixOutputThreeColumnTailSelectedData 111 j : ℤ) := by decide +kernel

private theorem selected_row112 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 112 j%101=(sixOutputThreeColumnTailSelectedData 112 j : ℤ) := by decide +kernel

private theorem selected_row113 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 113 j%101=(sixOutputThreeColumnTailSelectedData 113 j : ℤ) := by decide +kernel

private theorem selected_row114 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 114 j%101=(sixOutputThreeColumnTailSelectedData 114 j : ℤ) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnTailSelectedIntegerEntry sixOutputThreeColumnTailSelectedData

theorem sixOutputThreeColumnTail_selected_integer_rows_22 (i j : Fin 120)
    (hlo : 110 ≤ i.val) (hhi : i.val < 115) :
    sixOutputThreeColumnTailSelectedIntegerEntry i j%101=(sixOutputThreeColumnTailSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row110 j
  · exact selected_row111 j
  · exact selected_row112 j
  · exact selected_row113 j
  · exact selected_row114 j

end FD56
