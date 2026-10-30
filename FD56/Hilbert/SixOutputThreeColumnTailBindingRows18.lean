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

private theorem selected_row90 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 90 j%101=(sixOutputThreeColumnTailSelectedData 90 j : ℤ) := by decide +kernel

private theorem selected_row91 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 91 j%101=(sixOutputThreeColumnTailSelectedData 91 j : ℤ) := by decide +kernel

private theorem selected_row92 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 92 j%101=(sixOutputThreeColumnTailSelectedData 92 j : ℤ) := by decide +kernel

private theorem selected_row93 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 93 j%101=(sixOutputThreeColumnTailSelectedData 93 j : ℤ) := by decide +kernel

private theorem selected_row94 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 94 j%101=(sixOutputThreeColumnTailSelectedData 94 j : ℤ) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnTailSelectedIntegerEntry sixOutputThreeColumnTailSelectedData

theorem sixOutputThreeColumnTail_selected_integer_rows_18 (i j : Fin 120)
    (hlo : 90 ≤ i.val) (hhi : i.val < 95) :
    sixOutputThreeColumnTailSelectedIntegerEntry i j%101=(sixOutputThreeColumnTailSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row90 j
  · exact selected_row91 j
  · exact selected_row92 j
  · exact selected_row93 j
  · exact selected_row94 j

end FD56
