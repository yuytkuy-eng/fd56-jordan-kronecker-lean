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

private theorem selected_row80 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 80 j%101=(sixOutputThreeColumnTailSelectedData 80 j : ℤ) := by decide +kernel

private theorem selected_row81 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 81 j%101=(sixOutputThreeColumnTailSelectedData 81 j : ℤ) := by decide +kernel

private theorem selected_row82 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 82 j%101=(sixOutputThreeColumnTailSelectedData 82 j : ℤ) := by decide +kernel

private theorem selected_row83 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 83 j%101=(sixOutputThreeColumnTailSelectedData 83 j : ℤ) := by decide +kernel

private theorem selected_row84 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 84 j%101=(sixOutputThreeColumnTailSelectedData 84 j : ℤ) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnTailSelectedIntegerEntry sixOutputThreeColumnTailSelectedData

theorem sixOutputThreeColumnTail_selected_integer_rows_16 (i j : Fin 120)
    (hlo : 80 ≤ i.val) (hhi : i.val < 85) :
    sixOutputThreeColumnTailSelectedIntegerEntry i j%101=(sixOutputThreeColumnTailSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row80 j
  · exact selected_row81 j
  · exact selected_row82 j
  · exact selected_row83 j
  · exact selected_row84 j

end FD56
