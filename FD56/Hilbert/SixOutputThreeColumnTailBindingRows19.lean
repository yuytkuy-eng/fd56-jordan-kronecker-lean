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

private theorem selected_row95 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 95 j%101=(sixOutputThreeColumnTailSelectedData 95 j : ℤ) := by decide +kernel

private theorem selected_row96 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 96 j%101=(sixOutputThreeColumnTailSelectedData 96 j : ℤ) := by decide +kernel

private theorem selected_row97 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 97 j%101=(sixOutputThreeColumnTailSelectedData 97 j : ℤ) := by decide +kernel

private theorem selected_row98 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 98 j%101=(sixOutputThreeColumnTailSelectedData 98 j : ℤ) := by decide +kernel

private theorem selected_row99 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 99 j%101=(sixOutputThreeColumnTailSelectedData 99 j : ℤ) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnTailSelectedIntegerEntry sixOutputThreeColumnTailSelectedData

theorem sixOutputThreeColumnTail_selected_integer_rows_19 (i j : Fin 120)
    (hlo : 95 ≤ i.val) (hhi : i.val < 100) :
    sixOutputThreeColumnTailSelectedIntegerEntry i j%101=(sixOutputThreeColumnTailSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row95 j
  · exact selected_row96 j
  · exact selected_row97 j
  · exact selected_row98 j
  · exact selected_row99 j

end FD56
