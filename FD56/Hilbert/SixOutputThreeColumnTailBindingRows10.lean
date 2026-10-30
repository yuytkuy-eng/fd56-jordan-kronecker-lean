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

private theorem selected_row50 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 50 j%101=(sixOutputThreeColumnTailSelectedData 50 j : ℤ) := by decide +kernel

private theorem selected_row51 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 51 j%101=(sixOutputThreeColumnTailSelectedData 51 j : ℤ) := by decide +kernel

private theorem selected_row52 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 52 j%101=(sixOutputThreeColumnTailSelectedData 52 j : ℤ) := by decide +kernel

private theorem selected_row53 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 53 j%101=(sixOutputThreeColumnTailSelectedData 53 j : ℤ) := by decide +kernel

private theorem selected_row54 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 54 j%101=(sixOutputThreeColumnTailSelectedData 54 j : ℤ) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnTailSelectedIntegerEntry sixOutputThreeColumnTailSelectedData

theorem sixOutputThreeColumnTail_selected_integer_rows_10 (i j : Fin 120)
    (hlo : 50 ≤ i.val) (hhi : i.val < 55) :
    sixOutputThreeColumnTailSelectedIntegerEntry i j%101=(sixOutputThreeColumnTailSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row50 j
  · exact selected_row51 j
  · exact selected_row52 j
  · exact selected_row53 j
  · exact selected_row54 j

end FD56
