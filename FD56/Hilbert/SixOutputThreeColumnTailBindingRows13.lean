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

private theorem selected_row65 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 65 j%101=(sixOutputThreeColumnTailSelectedData 65 j : ℤ) := by decide +kernel

private theorem selected_row66 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 66 j%101=(sixOutputThreeColumnTailSelectedData 66 j : ℤ) := by decide +kernel

private theorem selected_row67 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 67 j%101=(sixOutputThreeColumnTailSelectedData 67 j : ℤ) := by decide +kernel

private theorem selected_row68 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 68 j%101=(sixOutputThreeColumnTailSelectedData 68 j : ℤ) := by decide +kernel

private theorem selected_row69 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 69 j%101=(sixOutputThreeColumnTailSelectedData 69 j : ℤ) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnTailSelectedIntegerEntry sixOutputThreeColumnTailSelectedData

theorem sixOutputThreeColumnTail_selected_integer_rows_13 (i j : Fin 120)
    (hlo : 65 ≤ i.val) (hhi : i.val < 70) :
    sixOutputThreeColumnTailSelectedIntegerEntry i j%101=(sixOutputThreeColumnTailSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row65 j
  · exact selected_row66 j
  · exact selected_row67 j
  · exact selected_row68 j
  · exact selected_row69 j

end FD56
