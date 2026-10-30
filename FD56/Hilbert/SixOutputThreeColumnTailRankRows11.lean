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

private theorem inverse_row55 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 55) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (55:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row56 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 56) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (56:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row57 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 57) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (57:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row58 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 58) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (58:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row59 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 59) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (59:Fin 120)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnTailInverseRows sixOutputThreeColumnTailSelectedColumns

theorem sixOutputThreeColumnTail_inverse_residue_rows_11 (i j : Fin 120)
    (hlo : 55 ≤ i.val) (hhi : i.val < 60) :
    natListDot (sixOutputThreeColumnTailInverseRows i) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row55 j
  · exact inverse_row56 j
  · exact inverse_row57 j
  · exact inverse_row58 j
  · exact inverse_row59 j

end FD56
