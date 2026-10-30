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

private theorem selected_row75 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 75 j%101=(sixOutputThreeColumnTailSelectedData 75 j : ℤ) := by decide +kernel

private theorem selected_row76 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 76 j%101=(sixOutputThreeColumnTailSelectedData 76 j : ℤ) := by decide +kernel

private theorem selected_row77 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 77 j%101=(sixOutputThreeColumnTailSelectedData 77 j : ℤ) := by decide +kernel

private theorem selected_row78 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 78 j%101=(sixOutputThreeColumnTailSelectedData 78 j : ℤ) := by decide +kernel

private theorem selected_row79 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 79 j%101=(sixOutputThreeColumnTailSelectedData 79 j : ℤ) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnTailSelectedIntegerEntry sixOutputThreeColumnTailSelectedData

theorem sixOutputThreeColumnTail_selected_integer_rows_15 (i j : Fin 120)
    (hlo : 75 ≤ i.val) (hhi : i.val < 80) :
    sixOutputThreeColumnTailSelectedIntegerEntry i j%101=(sixOutputThreeColumnTailSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row75 j
  · exact selected_row76 j
  · exact selected_row77 j
  · exact selected_row78 j
  · exact selected_row79 j

end FD56
