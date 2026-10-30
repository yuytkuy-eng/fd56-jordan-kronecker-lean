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

private theorem inverse_row15 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 15) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (15:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row16 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 16) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (16:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row17 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 17) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (17:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row18 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 18) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (18:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row19 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 19) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (19:Fin 120)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnTailInverseRows sixOutputThreeColumnTailSelectedColumns

theorem sixOutputThreeColumnTail_inverse_residue_rows_3 (i j : Fin 120)
    (hlo : 15 ≤ i.val) (hhi : i.val < 20) :
    natListDot (sixOutputThreeColumnTailInverseRows i) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row15 j
  · exact inverse_row16 j
  · exact inverse_row17 j
  · exact inverse_row18 j
  · exact inverse_row19 j

end FD56
