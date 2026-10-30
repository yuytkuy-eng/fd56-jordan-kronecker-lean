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

private theorem inverse_row45 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 45) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (45:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row46 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 46) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (46:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row47 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 47) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (47:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row48 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 48) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (48:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row49 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 49) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (49:Fin 120)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnTailInverseRows sixOutputThreeColumnTailSelectedColumns

theorem sixOutputThreeColumnTail_inverse_residue_rows_9 (i j : Fin 120)
    (hlo : 45 ≤ i.val) (hhi : i.val < 50) :
    natListDot (sixOutputThreeColumnTailInverseRows i) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row45 j
  · exact inverse_row46 j
  · exact inverse_row47 j
  · exact inverse_row48 j
  · exact inverse_row49 j

end FD56
