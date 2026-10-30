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

private theorem selected_row10 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 10 j%101=(sixOutputThreeColumnTailSelectedData 10 j : ℤ) := by decide +kernel

private theorem selected_row11 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 11 j%101=(sixOutputThreeColumnTailSelectedData 11 j : ℤ) := by decide +kernel

private theorem selected_row12 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 12 j%101=(sixOutputThreeColumnTailSelectedData 12 j : ℤ) := by decide +kernel

private theorem selected_row13 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 13 j%101=(sixOutputThreeColumnTailSelectedData 13 j : ℤ) := by decide +kernel

private theorem selected_row14 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 14 j%101=(sixOutputThreeColumnTailSelectedData 14 j : ℤ) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnTailSelectedIntegerEntry sixOutputThreeColumnTailSelectedData

theorem sixOutputThreeColumnTail_selected_integer_rows_2 (i j : Fin 120)
    (hlo : 10 ≤ i.val) (hhi : i.val < 15) :
    sixOutputThreeColumnTailSelectedIntegerEntry i j%101=(sixOutputThreeColumnTailSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row10 j
  · exact selected_row11 j
  · exact selected_row12 j
  · exact selected_row13 j
  · exact selected_row14 j

end FD56
