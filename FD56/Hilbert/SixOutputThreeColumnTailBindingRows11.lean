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

private theorem selected_row55 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 55 j%101=(sixOutputThreeColumnTailSelectedData 55 j : ℤ) := by decide +kernel

private theorem selected_row56 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 56 j%101=(sixOutputThreeColumnTailSelectedData 56 j : ℤ) := by decide +kernel

private theorem selected_row57 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 57 j%101=(sixOutputThreeColumnTailSelectedData 57 j : ℤ) := by decide +kernel

private theorem selected_row58 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 58 j%101=(sixOutputThreeColumnTailSelectedData 58 j : ℤ) := by decide +kernel

private theorem selected_row59 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 59 j%101=(sixOutputThreeColumnTailSelectedData 59 j : ℤ) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnTailSelectedIntegerEntry sixOutputThreeColumnTailSelectedData

theorem sixOutputThreeColumnTail_selected_integer_rows_11 (i j : Fin 120)
    (hlo : 55 ≤ i.val) (hhi : i.val < 60) :
    sixOutputThreeColumnTailSelectedIntegerEntry i j%101=(sixOutputThreeColumnTailSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row55 j
  · exact selected_row56 j
  · exact selected_row57 j
  · exact selected_row58 j
  · exact selected_row59 j

end FD56
