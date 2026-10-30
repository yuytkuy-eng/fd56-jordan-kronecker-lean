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

private theorem inverse_row25 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 25) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (25:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row26 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 26) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (26:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row27 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 27) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (27:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row28 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 28) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (28:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row29 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 29) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (29:Fin 120)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnTailInverseRows sixOutputThreeColumnTailSelectedColumns

theorem sixOutputThreeColumnTail_inverse_residue_rows_5 (i j : Fin 120)
    (hlo : 25 ≤ i.val) (hhi : i.val < 30) :
    natListDot (sixOutputThreeColumnTailInverseRows i) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row25 j
  · exact inverse_row26 j
  · exact inverse_row27 j
  · exact inverse_row28 j
  · exact inverse_row29 j

end FD56
