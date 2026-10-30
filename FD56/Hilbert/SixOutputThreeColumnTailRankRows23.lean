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

private theorem inverse_row115 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 115) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (115:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row116 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 116) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (116:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row117 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 117) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (117:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row118 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 118) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (118:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row119 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 119) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (119:Fin 120)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnTailInverseRows sixOutputThreeColumnTailSelectedColumns

theorem sixOutputThreeColumnTail_inverse_residue_rows_23 (i j : Fin 120)
    (hlo : 115 ≤ i.val) (hhi : i.val < 120) :
    natListDot (sixOutputThreeColumnTailInverseRows i) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row115 j
  · exact inverse_row116 j
  · exact inverse_row117 j
  · exact inverse_row118 j
  · exact inverse_row119 j

end FD56
