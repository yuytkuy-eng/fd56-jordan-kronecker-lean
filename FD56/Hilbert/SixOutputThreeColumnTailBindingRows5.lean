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

private theorem selected_row25 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 25 j%101=(sixOutputThreeColumnTailSelectedData 25 j : ℤ) := by decide +kernel

private theorem selected_row26 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 26 j%101=(sixOutputThreeColumnTailSelectedData 26 j : ℤ) := by decide +kernel

private theorem selected_row27 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 27 j%101=(sixOutputThreeColumnTailSelectedData 27 j : ℤ) := by decide +kernel

private theorem selected_row28 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 28 j%101=(sixOutputThreeColumnTailSelectedData 28 j : ℤ) := by decide +kernel

private theorem selected_row29 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 29 j%101=(sixOutputThreeColumnTailSelectedData 29 j : ℤ) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnTailSelectedIntegerEntry sixOutputThreeColumnTailSelectedData

theorem sixOutputThreeColumnTail_selected_integer_rows_5 (i j : Fin 120)
    (hlo : 25 ≤ i.val) (hhi : i.val < 30) :
    sixOutputThreeColumnTailSelectedIntegerEntry i j%101=(sixOutputThreeColumnTailSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row25 j
  · exact selected_row26 j
  · exact selected_row27 j
  · exact selected_row28 j
  · exact selected_row29 j

end FD56
