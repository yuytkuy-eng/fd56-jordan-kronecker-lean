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

private theorem selected_row115 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 115 j%101=(sixOutputThreeColumnTailSelectedData 115 j : ℤ) := by decide +kernel

private theorem selected_row116 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 116 j%101=(sixOutputThreeColumnTailSelectedData 116 j : ℤ) := by decide +kernel

private theorem selected_row117 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 117 j%101=(sixOutputThreeColumnTailSelectedData 117 j : ℤ) := by decide +kernel

private theorem selected_row118 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 118 j%101=(sixOutputThreeColumnTailSelectedData 118 j : ℤ) := by decide +kernel

private theorem selected_row119 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 119 j%101=(sixOutputThreeColumnTailSelectedData 119 j : ℤ) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnTailSelectedIntegerEntry sixOutputThreeColumnTailSelectedData

theorem sixOutputThreeColumnTail_selected_integer_rows_23 (i j : Fin 120)
    (hlo : 115 ≤ i.val) (hhi : i.val < 120) :
    sixOutputThreeColumnTailSelectedIntegerEntry i j%101=(sixOutputThreeColumnTailSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row115 j
  · exact selected_row116 j
  · exact selected_row117 j
  · exact selected_row118 j
  · exact selected_row119 j

end FD56
