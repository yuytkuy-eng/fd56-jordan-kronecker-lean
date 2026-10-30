/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputThreeColumnTailData

/-! Five rows of the kernel-checked selected inverse. -/

namespace FD56
open Matrix
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 12000000

private theorem inverse_row10 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 10) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (10:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row11 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 11) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (11:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row12 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 12) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (12:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row13 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 13) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (13:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row14 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 14) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (14:Fin 120)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnTailInverseRows sixOutputThreeColumnTailSelectedColumns

theorem sixOutputThreeColumnTail_inverse_residue_rows_2 (i j : Fin 120)
    (hlo : 10 ≤ i.val) (hhi : i.val < 15) :
    natListDot (sixOutputThreeColumnTailInverseRows i) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row10 j
  · exact inverse_row11 j
  · exact inverse_row12 j
  · exact inverse_row13 j
  · exact inverse_row14 j

end FD56
