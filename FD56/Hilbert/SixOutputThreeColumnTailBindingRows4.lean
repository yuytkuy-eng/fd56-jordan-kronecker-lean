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

private theorem selected_row20 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 20 j%101=(sixOutputThreeColumnTailSelectedData 20 j : ℤ) := by decide +kernel

private theorem selected_row21 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 21 j%101=(sixOutputThreeColumnTailSelectedData 21 j : ℤ) := by decide +kernel

private theorem selected_row22 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 22 j%101=(sixOutputThreeColumnTailSelectedData 22 j : ℤ) := by decide +kernel

private theorem selected_row23 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 23 j%101=(sixOutputThreeColumnTailSelectedData 23 j : ℤ) := by decide +kernel

private theorem selected_row24 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 24 j%101=(sixOutputThreeColumnTailSelectedData 24 j : ℤ) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnTailSelectedIntegerEntry sixOutputThreeColumnTailSelectedData

theorem sixOutputThreeColumnTail_selected_integer_rows_4 (i j : Fin 120)
    (hlo : 20 ≤ i.val) (hhi : i.val < 25) :
    sixOutputThreeColumnTailSelectedIntegerEntry i j%101=(sixOutputThreeColumnTailSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row20 j
  · exact selected_row21 j
  · exact selected_row22 j
  · exact selected_row23 j
  · exact selected_row24 j

end FD56
