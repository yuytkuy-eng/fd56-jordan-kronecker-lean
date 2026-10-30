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

private theorem inverse_row60 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 60) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (60:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row61 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 61) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (61:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row62 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 62) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (62:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row63 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 63) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (63:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row64 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 64) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (64:Fin 120)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnTailInverseRows sixOutputThreeColumnTailSelectedColumns

theorem sixOutputThreeColumnTail_inverse_residue_rows_12 (i j : Fin 120)
    (hlo : 60 ≤ i.val) (hhi : i.val < 65) :
    natListDot (sixOutputThreeColumnTailInverseRows i) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row60 j
  · exact inverse_row61 j
  · exact inverse_row62 j
  · exact inverse_row63 j
  · exact inverse_row64 j

end FD56
