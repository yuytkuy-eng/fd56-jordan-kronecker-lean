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

private theorem selected_row60 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 60 j%101=(sixOutputThreeColumnTailSelectedData 60 j : ℤ) := by decide +kernel

private theorem selected_row61 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 61 j%101=(sixOutputThreeColumnTailSelectedData 61 j : ℤ) := by decide +kernel

private theorem selected_row62 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 62 j%101=(sixOutputThreeColumnTailSelectedData 62 j : ℤ) := by decide +kernel

private theorem selected_row63 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 63 j%101=(sixOutputThreeColumnTailSelectedData 63 j : ℤ) := by decide +kernel

private theorem selected_row64 : ∀ j : Fin 120,
    sixOutputThreeColumnTailSelectedIntegerEntry 64 j%101=(sixOutputThreeColumnTailSelectedData 64 j : ℤ) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnTailSelectedIntegerEntry sixOutputThreeColumnTailSelectedData

theorem sixOutputThreeColumnTail_selected_integer_rows_12 (i j : Fin 120)
    (hlo : 60 ≤ i.val) (hhi : i.val < 65) :
    sixOutputThreeColumnTailSelectedIntegerEntry i j%101=(sixOutputThreeColumnTailSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row60 j
  · exact selected_row61 j
  · exact selected_row62 j
  · exact selected_row63 j
  · exact selected_row64 j

end FD56
