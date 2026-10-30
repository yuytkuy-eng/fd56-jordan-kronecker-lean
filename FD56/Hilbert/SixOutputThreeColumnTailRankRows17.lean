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

private theorem inverse_row85 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 85) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (85:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row86 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 86) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (86:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row87 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 87) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (87:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row88 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 88) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (88:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row89 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 89) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (89:Fin 120)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnTailInverseRows sixOutputThreeColumnTailSelectedColumns

theorem sixOutputThreeColumnTail_inverse_residue_rows_17 (i j : Fin 120)
    (hlo : 85 ≤ i.val) (hhi : i.val < 90) :
    natListDot (sixOutputThreeColumnTailInverseRows i) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row85 j
  · exact inverse_row86 j
  · exact inverse_row87 j
  · exact inverse_row88 j
  · exact inverse_row89 j

end FD56
