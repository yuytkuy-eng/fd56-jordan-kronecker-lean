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

private theorem inverse_row75 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 75) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (75:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row76 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 76) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (76:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row77 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 77) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (77:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row78 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 78) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (78:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row79 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 79) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (79:Fin 120)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnTailInverseRows sixOutputThreeColumnTailSelectedColumns

theorem sixOutputThreeColumnTail_inverse_residue_rows_15 (i j : Fin 120)
    (hlo : 75 ≤ i.val) (hhi : i.val < 80) :
    natListDot (sixOutputThreeColumnTailInverseRows i) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row75 j
  · exact inverse_row76 j
  · exact inverse_row77 j
  · exact inverse_row78 j
  · exact inverse_row79 j

end FD56
