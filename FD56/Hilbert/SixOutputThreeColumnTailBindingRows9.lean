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

private theorem selected_row45 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 45 j%101=(sixOutputThreeColumnTailSelectedData 45 j : ℤ) := by decide +kernel

private theorem selected_row46 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 46 j%101=(sixOutputThreeColumnTailSelectedData 46 j : ℤ) := by decide +kernel

private theorem selected_row47 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 47 j%101=(sixOutputThreeColumnTailSelectedData 47 j : ℤ) := by decide +kernel

private theorem selected_row48 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 48 j%101=(sixOutputThreeColumnTailSelectedData 48 j : ℤ) := by decide +kernel

private theorem selected_row49 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 49 j%101=(sixOutputThreeColumnTailSelectedData 49 j : ℤ) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnTailSelectedIntegerEntry sixOutputThreeColumnTailSelectedData

theorem sixOutputThreeColumnTail_selected_integer_rows_9 (i j : Fin 120)
    (hlo : 45 ≤ i.val) (hhi : i.val < 50) :
    sixOutputThreeColumnTailSelectedIntegerEntry i j%101=(sixOutputThreeColumnTailSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row45 j
  · exact selected_row46 j
  · exact selected_row47 j
  · exact selected_row48 j
  · exact selected_row49 j

end FD56
