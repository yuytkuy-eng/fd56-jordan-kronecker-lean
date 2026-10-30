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

private theorem inverse_row105 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 105) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (105:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row106 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 106) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (106:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row107 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 107) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (107:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row108 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 108) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (108:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row109 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 109) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (109:Fin 120)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnTailInverseRows sixOutputThreeColumnTailSelectedColumns

theorem sixOutputThreeColumnTail_inverse_residue_rows_21 (i j : Fin 120)
    (hlo : 105 ≤ i.val) (hhi : i.val < 110) :
    natListDot (sixOutputThreeColumnTailInverseRows i) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row105 j
  · exact inverse_row106 j
  · exact inverse_row107 j
  · exact inverse_row108 j
  · exact inverse_row109 j

end FD56
