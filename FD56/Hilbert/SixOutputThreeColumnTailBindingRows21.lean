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

private theorem selected_row105 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 105 j%101=(sixOutputThreeColumnTailSelectedData 105 j : ℤ) := by decide +kernel

private theorem selected_row106 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 106 j%101=(sixOutputThreeColumnTailSelectedData 106 j : ℤ) := by decide +kernel

private theorem selected_row107 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 107 j%101=(sixOutputThreeColumnTailSelectedData 107 j : ℤ) := by decide +kernel

private theorem selected_row108 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 108 j%101=(sixOutputThreeColumnTailSelectedData 108 j : ℤ) := by decide +kernel

private theorem selected_row109 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 109 j%101=(sixOutputThreeColumnTailSelectedData 109 j : ℤ) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnTailSelectedIntegerEntry sixOutputThreeColumnTailSelectedData

theorem sixOutputThreeColumnTail_selected_integer_rows_21 (i j : Fin 120)
    (hlo : 105 ≤ i.val) (hhi : i.val < 110) :
    sixOutputThreeColumnTailSelectedIntegerEntry i j%101=(sixOutputThreeColumnTailSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row105 j
  · exact selected_row106 j
  · exact selected_row107 j
  · exact selected_row108 j
  · exact selected_row109 j

end FD56
