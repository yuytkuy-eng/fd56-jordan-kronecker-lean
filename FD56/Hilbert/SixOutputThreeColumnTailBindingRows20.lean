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

private theorem selected_row100 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 100 j%101=(sixOutputThreeColumnTailSelectedData 100 j : ℤ) := by decide +kernel

private theorem selected_row101 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 101 j%101=(sixOutputThreeColumnTailSelectedData 101 j : ℤ) := by decide +kernel

private theorem selected_row102 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 102 j%101=(sixOutputThreeColumnTailSelectedData 102 j : ℤ) := by decide +kernel

private theorem selected_row103 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 103 j%101=(sixOutputThreeColumnTailSelectedData 103 j : ℤ) := by decide +kernel

private theorem selected_row104 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 104 j%101=(sixOutputThreeColumnTailSelectedData 104 j : ℤ) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnTailSelectedIntegerEntry sixOutputThreeColumnTailSelectedData

theorem sixOutputThreeColumnTail_selected_integer_rows_20 (i j : Fin 120)
    (hlo : 100 ≤ i.val) (hhi : i.val < 105) :
    sixOutputThreeColumnTailSelectedIntegerEntry i j%101=(sixOutputThreeColumnTailSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row100 j
  · exact selected_row101 j
  · exact selected_row102 j
  · exact selected_row103 j
  · exact selected_row104 j

end FD56
