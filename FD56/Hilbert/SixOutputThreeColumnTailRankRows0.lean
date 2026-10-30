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

private theorem inverse_row0 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 0) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (0:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row1 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 1) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (1:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row2 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 2) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (2:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row3 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 3) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (3:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row4 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 4) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (4:Fin 120)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnTailInverseRows sixOutputThreeColumnTailSelectedColumns

theorem sixOutputThreeColumnTail_inverse_residue_rows_0 (i j : Fin 120)
    (hlo : 0 ≤ i.val) (hhi : i.val < 5) :
    natListDot (sixOutputThreeColumnTailInverseRows i) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row0 j
  · exact inverse_row1 j
  · exact inverse_row2 j
  · exact inverse_row3 j
  · exact inverse_row4 j

end FD56
