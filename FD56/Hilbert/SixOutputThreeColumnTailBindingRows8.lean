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

private theorem selected_row40 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 40 j%101=(sixOutputThreeColumnTailSelectedData 40 j : ℤ) := by decide +kernel

private theorem selected_row41 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 41 j%101=(sixOutputThreeColumnTailSelectedData 41 j : ℤ) := by decide +kernel

private theorem selected_row42 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 42 j%101=(sixOutputThreeColumnTailSelectedData 42 j : ℤ) := by decide +kernel

private theorem selected_row43 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 43 j%101=(sixOutputThreeColumnTailSelectedData 43 j : ℤ) := by decide +kernel

private theorem selected_row44 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 44 j%101=(sixOutputThreeColumnTailSelectedData 44 j : ℤ) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnTailSelectedIntegerEntry sixOutputThreeColumnTailSelectedData

theorem sixOutputThreeColumnTail_selected_integer_rows_8 (i j : Fin 120)
    (hlo : 40 ≤ i.val) (hhi : i.val < 45) :
    sixOutputThreeColumnTailSelectedIntegerEntry i j%101=(sixOutputThreeColumnTailSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row40 j
  · exact selected_row41 j
  · exact selected_row42 j
  · exact selected_row43 j
  · exact selected_row44 j

end FD56
