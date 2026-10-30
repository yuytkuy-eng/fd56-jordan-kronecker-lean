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

private theorem inverse_row20 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 20) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (20:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row21 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 21) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (21:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row22 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 22) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (22:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row23 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 23) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (23:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row24 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 24) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (24:Fin 120)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnTailInverseRows sixOutputThreeColumnTailSelectedColumns

theorem sixOutputThreeColumnTail_inverse_residue_rows_4 (i j : Fin 120)
    (hlo : 20 ≤ i.val) (hhi : i.val < 25) :
    natListDot (sixOutputThreeColumnTailInverseRows i) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row20 j
  · exact inverse_row21 j
  · exact inverse_row22 j
  · exact inverse_row23 j
  · exact inverse_row24 j

end FD56
