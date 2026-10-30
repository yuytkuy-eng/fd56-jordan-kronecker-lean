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

private theorem inverse_row30 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 30) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (30:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row31 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 31) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (31:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row32 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 32) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (32:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row33 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 33) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (33:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row34 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 34) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (34:Fin 120)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnTailInverseRows sixOutputThreeColumnTailSelectedColumns

theorem sixOutputThreeColumnTail_inverse_residue_rows_6 (i j : Fin 120)
    (hlo : 30 ≤ i.val) (hhi : i.val < 35) :
    natListDot (sixOutputThreeColumnTailInverseRows i) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row30 j
  · exact inverse_row31 j
  · exact inverse_row32 j
  · exact inverse_row33 j
  · exact inverse_row34 j

end FD56
