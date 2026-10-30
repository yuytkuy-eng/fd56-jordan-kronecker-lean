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

private theorem inverse_row100 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 100) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (100:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row101 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 101) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (101:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row102 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 102) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (102:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row103 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 103) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (103:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row104 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 104) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (104:Fin 120)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnTailInverseRows sixOutputThreeColumnTailSelectedColumns

theorem sixOutputThreeColumnTail_inverse_residue_rows_20 (i j : Fin 120)
    (hlo : 100 ≤ i.val) (hhi : i.val < 105) :
    natListDot (sixOutputThreeColumnTailInverseRows i) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row100 j
  · exact inverse_row101 j
  · exact inverse_row102 j
  · exact inverse_row103 j
  · exact inverse_row104 j

end FD56
