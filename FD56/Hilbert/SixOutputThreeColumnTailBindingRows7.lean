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

private theorem selected_row35 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 35 j%101=(sixOutputThreeColumnTailSelectedData 35 j : ℤ) := by decide +kernel

private theorem selected_row36 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 36 j%101=(sixOutputThreeColumnTailSelectedData 36 j : ℤ) := by decide +kernel

private theorem selected_row37 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 37 j%101=(sixOutputThreeColumnTailSelectedData 37 j : ℤ) := by decide +kernel

private theorem selected_row38 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 38 j%101=(sixOutputThreeColumnTailSelectedData 38 j : ℤ) := by decide +kernel

private theorem selected_row39 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 39 j%101=(sixOutputThreeColumnTailSelectedData 39 j : ℤ) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnTailSelectedIntegerEntry sixOutputThreeColumnTailSelectedData

theorem sixOutputThreeColumnTail_selected_integer_rows_7 (i j : Fin 120)
    (hlo : 35 ≤ i.val) (hhi : i.val < 40) :
    sixOutputThreeColumnTailSelectedIntegerEntry i j%101=(sixOutputThreeColumnTailSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row35 j
  · exact selected_row36 j
  · exact selected_row37 j
  · exact selected_row38 j
  · exact selected_row39 j

end FD56
