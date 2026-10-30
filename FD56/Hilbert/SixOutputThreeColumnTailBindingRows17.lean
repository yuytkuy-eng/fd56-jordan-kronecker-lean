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

private theorem selected_row85 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 85 j%101=(sixOutputThreeColumnTailSelectedData 85 j : ℤ) := by decide +kernel

private theorem selected_row86 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 86 j%101=(sixOutputThreeColumnTailSelectedData 86 j : ℤ) := by decide +kernel

private theorem selected_row87 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 87 j%101=(sixOutputThreeColumnTailSelectedData 87 j : ℤ) := by decide +kernel

private theorem selected_row88 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 88 j%101=(sixOutputThreeColumnTailSelectedData 88 j : ℤ) := by decide +kernel

private theorem selected_row89 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 89 j%101=(sixOutputThreeColumnTailSelectedData 89 j : ℤ) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnTailSelectedIntegerEntry sixOutputThreeColumnTailSelectedData

theorem sixOutputThreeColumnTail_selected_integer_rows_17 (i j : Fin 120)
    (hlo : 85 ≤ i.val) (hhi : i.val < 90) :
    sixOutputThreeColumnTailSelectedIntegerEntry i j%101=(sixOutputThreeColumnTailSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row85 j
  · exact selected_row86 j
  · exact selected_row87 j
  · exact selected_row88 j
  · exact selected_row89 j

end FD56
