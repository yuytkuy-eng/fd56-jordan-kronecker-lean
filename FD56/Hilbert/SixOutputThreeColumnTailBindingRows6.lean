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

private theorem selected_row30 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 30 j%101=(sixOutputThreeColumnTailSelectedData 30 j : ℤ) := by decide +kernel

private theorem selected_row31 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 31 j%101=(sixOutputThreeColumnTailSelectedData 31 j : ℤ) := by decide +kernel

private theorem selected_row32 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 32 j%101=(sixOutputThreeColumnTailSelectedData 32 j : ℤ) := by decide +kernel

private theorem selected_row33 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 33 j%101=(sixOutputThreeColumnTailSelectedData 33 j : ℤ) := by decide +kernel

private theorem selected_row34 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 34 j%101=(sixOutputThreeColumnTailSelectedData 34 j : ℤ) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnTailSelectedIntegerEntry sixOutputThreeColumnTailSelectedData

theorem sixOutputThreeColumnTail_selected_integer_rows_6 (i j : Fin 120)
    (hlo : 30 ≤ i.val) (hhi : i.val < 35) :
    sixOutputThreeColumnTailSelectedIntegerEntry i j%101=(sixOutputThreeColumnTailSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row30 j
  · exact selected_row31 j
  · exact selected_row32 j
  · exact selected_row33 j
  · exact selected_row34 j

end FD56
