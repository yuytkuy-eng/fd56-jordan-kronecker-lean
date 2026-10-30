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

private theorem inverse_row95 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 95) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (95:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row96 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 96) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (96:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row97 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 97) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (97:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row98 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 98) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (98:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row99 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 99) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (99:Fin 120)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnTailInverseRows sixOutputThreeColumnTailSelectedColumns

theorem sixOutputThreeColumnTail_inverse_residue_rows_19 (i j : Fin 120)
    (hlo : 95 ≤ i.val) (hhi : i.val < 100) :
    natListDot (sixOutputThreeColumnTailInverseRows i) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row95 j
  · exact inverse_row96 j
  · exact inverse_row97 j
  · exact inverse_row98 j
  · exact inverse_row99 j

end FD56
