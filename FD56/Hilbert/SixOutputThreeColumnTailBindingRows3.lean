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

private theorem selected_row15 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 15 j%101=(sixOutputThreeColumnTailSelectedData 15 j : ℤ) := by decide +kernel

private theorem selected_row16 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 16 j%101=(sixOutputThreeColumnTailSelectedData 16 j : ℤ) := by decide +kernel

private theorem selected_row17 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 17 j%101=(sixOutputThreeColumnTailSelectedData 17 j : ℤ) := by decide +kernel

private theorem selected_row18 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 18 j%101=(sixOutputThreeColumnTailSelectedData 18 j : ℤ) := by decide +kernel

private theorem selected_row19 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 19 j%101=(sixOutputThreeColumnTailSelectedData 19 j : ℤ) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnTailSelectedIntegerEntry sixOutputThreeColumnTailSelectedData

theorem sixOutputThreeColumnTail_selected_integer_rows_3 (i j : Fin 120)
    (hlo : 15 ≤ i.val) (hhi : i.val < 20) :
    sixOutputThreeColumnTailSelectedIntegerEntry i j%101=(sixOutputThreeColumnTailSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row15 j
  · exact selected_row16 j
  · exact selected_row17 j
  · exact selected_row18 j
  · exact selected_row19 j

end FD56
