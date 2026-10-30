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

private theorem inverse_row110 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 110) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (110:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row111 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 111) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (111:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row112 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 112) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (112:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row113 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 113) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (113:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row114 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 114) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (114:Fin 120)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnTailInverseRows sixOutputThreeColumnTailSelectedColumns

theorem sixOutputThreeColumnTail_inverse_residue_rows_22 (i j : Fin 120)
    (hlo : 110 ≤ i.val) (hhi : i.val < 115) :
    natListDot (sixOutputThreeColumnTailInverseRows i) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row110 j
  · exact inverse_row111 j
  · exact inverse_row112 j
  · exact inverse_row113 j
  · exact inverse_row114 j

end FD56
