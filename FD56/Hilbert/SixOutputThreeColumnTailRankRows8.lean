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

private theorem inverse_row40 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 40) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (40:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row41 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 41) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (41:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row42 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 42) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (42:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row43 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 43) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (43:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row44 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 44) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (44:Fin 120)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnTailInverseRows sixOutputThreeColumnTailSelectedColumns

theorem sixOutputThreeColumnTail_inverse_residue_rows_8 (i j : Fin 120)
    (hlo : 40 ≤ i.val) (hhi : i.val < 45) :
    natListDot (sixOutputThreeColumnTailInverseRows i) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row40 j
  · exact inverse_row41 j
  · exact inverse_row42 j
  · exact inverse_row43 j
  · exact inverse_row44 j

end FD56
